use std::time::Duration;

use futures_util::stream::{FuturesUnordered, StreamExt};

use super::interface::{Decision, Environment, HandlerStep, ResourceManager, Unavailable, Vote};

const TIMEOUT: Duration = Duration::from_secs(1);

pub async fn handle(
    environment: &impl Environment,
    transaction_id: &str,
) -> Result<Decision, Unavailable> {
    environment.record(HandlerStep::Start);
    let decision = match environment.read_decision(transaction_id).await? {
        Some(decision) => decision,
        None => {
            environment.record(HandlerStep::Collect);
            let mut votes: FuturesUnordered<_> = environment
                .resource_managers()
                .iter()
                .enumerate()
                .map(|(rm, resource_manager)| async move {
                    environment.record(HandlerStep::RequestPrepare(rm));
                    (rm, resource_manager.prepare(transaction_id, TIMEOUT).await)
                })
                .collect();
            let (step, proposal) = loop {
                match votes.next().await {
                    Some((rm, Ok(Vote::Prepared))) => {
                        environment.record(HandlerStep::ReceivePrepared(rm))
                    }
                    Some((_, Ok(Vote::Refused))) => break (HandlerStep::Abort, Decision::Aborted),
                    Some((_, Err(Unavailable))) => break (HandlerStep::Timeout, Decision::Aborted),
                    None => break (HandlerStep::Commit, Decision::Committed),
                }
            };
            environment.record(step);
            environment.write_decision(transaction_id, proposal).await?
        }
    };
    environment.record(HandlerStep::Learn(decision));

    let mut informing: FuturesUnordered<_> = environment
        .resource_managers()
        .iter()
        .enumerate()
        .map(|(rm, resource_manager)| async move {
            environment.record(HandlerStep::Broadcast(rm));
            match decision {
                Decision::Committed => resource_manager.commit(transaction_id).await,
                Decision::Aborted => resource_manager.abort(transaction_id).await,
            }
        })
        .collect();
    let mut outcome = Ok(decision);
    while let Some(informed) = informing.next().await {
        if informed.is_err() {
            outcome = Err(Unavailable);
        }
    }
    outcome
}

#[cfg(test)]
mod tests {
    use std::future::pending;
    use std::sync::Mutex;
    use std::time::Duration;

    use futures_util::FutureExt;

    use super::handle;
    use crate::transaction_manager::interface::HandlerStep::*;
    use crate::transaction_manager::interface::{
        Database, Decision, Environment, HandlerLog, HandlerStep, ResourceManager, Unavailable,
        Vote,
    };

    struct TestResourceManager {
        vote: Option<Result<Vote, Unavailable>>,
        informed: Option<Result<(), Unavailable>>,
        received: Mutex<Vec<&'static str>>,
    }

    fn resource_manager(vote: Result<Vote, Unavailable>) -> TestResourceManager {
        TestResourceManager {
            vote: Some(vote),
            informed: Some(Ok(())),
            received: Mutex::default(),
        }
    }

    fn resource_manager_yet_to_vote() -> TestResourceManager {
        TestResourceManager {
            vote: None,
            informed: Some(Ok(())),
            received: Mutex::default(),
        }
    }

    impl ResourceManager for TestResourceManager {
        async fn prepare(&self, _: &str, _: Duration) -> Result<Vote, Unavailable> {
            self.received.lock().unwrap().push("prepare");
            match self.vote {
                Some(vote) => vote,
                None => pending().await,
            }
        }

        async fn commit(&self, _: &str) -> Result<(), Unavailable> {
            self.received.lock().unwrap().push("commit");
            match self.informed {
                Some(informed) => informed,
                None => pending().await,
            }
        }

        async fn abort(&self, _: &str) -> Result<(), Unavailable> {
            self.received.lock().unwrap().push("abort");
            match self.informed {
                Some(informed) => informed,
                None => pending().await,
            }
        }
    }

    enum OtherHandler {
        DecidesBeforeRead(Decision),
        DecidesBeforeWrite(Decision),
    }

    struct TestEnvironment {
        database_available: bool,
        other_handler: Option<OtherHandler>,
        decision: Mutex<Option<Decision>>,
        resource_managers: Vec<TestResourceManager>,
        steps: Mutex<Vec<HandlerStep>>,
    }

    fn environment(resource_managers: Vec<TestResourceManager>) -> TestEnvironment {
        TestEnvironment {
            database_available: true,
            other_handler: None,
            decision: Mutex::default(),
            resource_managers,
            steps: Mutex::default(),
        }
    }

    impl TestEnvironment {
        fn received(&self) -> Vec<String> {
            self.resource_managers
                .iter()
                .map(|resource_manager| resource_manager.received.lock().unwrap().join(" "))
                .collect()
        }

        fn steps(&self) -> Vec<HandlerStep> {
            self.steps.lock().unwrap().clone()
        }
    }

    impl HandlerLog for TestEnvironment {
        fn record(&self, step: HandlerStep) {
            self.steps.lock().unwrap().push(step);
        }
    }

    impl Database for TestEnvironment {
        async fn read_decision(&self, _: &str) -> Result<Option<Decision>, Unavailable> {
            if !self.database_available {
                return Err(Unavailable);
            }
            let mut stored = self.decision.lock().unwrap();
            if let Some(OtherHandler::DecidesBeforeRead(theirs)) = self.other_handler {
                stored.get_or_insert(theirs);
            }
            Ok(*stored)
        }

        async fn write_decision(
            &self,
            _: &str,
            decision: Decision,
        ) -> Result<Decision, Unavailable> {
            if !self.database_available {
                return Err(Unavailable);
            }
            let mut stored = self.decision.lock().unwrap();
            if let Some(OtherHandler::DecidesBeforeWrite(theirs)) = self.other_handler {
                stored.get_or_insert(theirs);
            }
            Ok(*stored.get_or_insert(decision))
        }
    }

    impl Environment for TestEnvironment {
        type ResourceManager = TestResourceManager;

        fn resource_managers(&self) -> &[TestResourceManager] {
            &self.resource_managers
        }
    }

    #[tokio::test]
    async fn commits_once_every_resource_manager_prepares() {
        let environment = environment(vec![
            resource_manager(Ok(Vote::Prepared)),
            resource_manager(Ok(Vote::Prepared)),
        ]);
        assert_eq!(handle(&environment, "t").await, Ok(Decision::Committed));
        assert_eq!(environment.received(), ["prepare commit", "prepare commit"]);
        assert_eq!(
            environment.steps(),
            [
                Start,
                Collect,
                RequestPrepare(0),
                ReceivePrepared(0),
                RequestPrepare(1),
                ReceivePrepared(1),
                Commit,
                Learn(Decision::Committed),
                Broadcast(0),
                Broadcast(1),
            ]
        );
    }

    #[test]
    fn aborts_as_soon_as_one_refuses() {
        let environment = environment(vec![
            resource_manager_yet_to_vote(),
            resource_manager(Ok(Vote::Refused)),
        ]);
        assert_eq!(
            handle(&environment, "t").now_or_never(),
            Some(Ok(Decision::Aborted))
        );
        assert_eq!(environment.received(), ["prepare abort", "prepare abort"]);
        assert_eq!(
            environment.steps(),
            [
                Start,
                Collect,
                RequestPrepare(0),
                RequestPrepare(1),
                Abort,
                Learn(Decision::Aborted),
                Broadcast(0),
                Broadcast(1),
            ]
        );
    }

    #[tokio::test]
    async fn aborts_when_one_is_unavailable() {
        let environment = environment(vec![
            resource_manager(Ok(Vote::Prepared)),
            resource_manager(Err(Unavailable)),
        ]);
        assert_eq!(handle(&environment, "t").await, Ok(Decision::Aborted));
        assert_eq!(environment.received(), ["prepare abort", "prepare abort"]);
        assert_eq!(
            environment.steps(),
            [
                Start,
                Collect,
                RequestPrepare(0),
                ReceivePrepared(0),
                RequestPrepare(1),
                Timeout,
                Learn(Decision::Aborted),
                Broadcast(0),
                Broadcast(1),
            ]
        );
    }

    #[tokio::test]
    async fn repeats_a_decision_already_made() {
        let environment = TestEnvironment {
            other_handler: Some(OtherHandler::DecidesBeforeRead(Decision::Committed)),
            ..environment(vec![resource_manager(Ok(Vote::Prepared))])
        };
        assert_eq!(handle(&environment, "t").await, Ok(Decision::Committed));
        assert_eq!(environment.received(), ["commit"]);
        assert_eq!(
            environment.steps(),
            [Start, Learn(Decision::Committed), Broadcast(0)]
        );
    }

    #[tokio::test]
    async fn follows_the_decision_that_stands() {
        let environment = TestEnvironment {
            other_handler: Some(OtherHandler::DecidesBeforeWrite(Decision::Aborted)),
            ..environment(vec![resource_manager(Ok(Vote::Prepared))])
        };
        assert_eq!(handle(&environment, "t").await, Ok(Decision::Aborted));
        assert_eq!(environment.received(), ["prepare abort"]);
        assert_eq!(
            environment.steps(),
            [
                Start,
                Collect,
                RequestPrepare(0),
                ReceivePrepared(0),
                Commit,
                Learn(Decision::Aborted),
                Broadcast(0),
            ]
        );
    }

    #[tokio::test]
    async fn is_unavailable_without_the_database() {
        let environment = TestEnvironment {
            database_available: false,
            ..environment(vec![resource_manager(Ok(Vote::Prepared))])
        };
        assert_eq!(handle(&environment, "t").await, Err(Unavailable));
        assert_eq!(environment.received(), [""]);
        assert_eq!(environment.steps(), [Start]);
    }

    #[tokio::test]
    async fn informs_the_rest_when_one_is_unavailable() {
        let environment = environment(vec![
            TestResourceManager {
                informed: Some(Err(Unavailable)),
                ..resource_manager(Ok(Vote::Prepared))
            },
            resource_manager(Ok(Vote::Prepared)),
        ]);
        assert_eq!(handle(&environment, "t").await, Err(Unavailable));
        assert_eq!(environment.received(), ["prepare commit", "prepare commit"]);
    }

    #[test]
    fn informs_every_resource_manager_at_once() {
        let environment = environment(vec![
            TestResourceManager {
                informed: None,
                ..resource_manager(Ok(Vote::Prepared))
            },
            resource_manager(Ok(Vote::Prepared)),
        ]);
        assert_eq!(handle(&environment, "t").now_or_never(), None);
        assert_eq!(environment.received(), ["prepare commit", "prepare commit"]);
    }

    #[test]
    fn handle_is_send() {
        fn is_send(_: impl Send) {}
        is_send(handle(&environment(vec![]), "t"));
    }
}
