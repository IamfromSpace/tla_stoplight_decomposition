use std::time::Duration;

use futures_util::stream::{FuturesUnordered, StreamExt};

use super::interface::{Decision, Environment, ResourceManager, Unavailable, Vote};

const TIMEOUT: Duration = Duration::from_secs(1);

pub async fn handle(
    environment: &impl Environment,
    transaction_id: &str,
) -> Result<Decision, Unavailable> {
    let decision = match environment.read_decision(transaction_id).await? {
        Some(decision) => decision,
        None => {
            let mut votes: FuturesUnordered<_> = environment
                .resource_managers()
                .iter()
                .map(|resource_manager| resource_manager.prepare(transaction_id, TIMEOUT))
                .collect();
            let mut proposal = Decision::Committed;
            while let Some(vote) = votes.next().await {
                match vote {
                    Ok(Vote::Prepared) => {}
                    Ok(Vote::Refused) | Err(Unavailable) => {
                        proposal = Decision::Aborted;
                        break;
                    }
                }
            }
            environment.write_decision(transaction_id, proposal).await?
        }
    };

    let mut informing: FuturesUnordered<_> = environment
        .resource_managers()
        .iter()
        .map(|resource_manager| async move {
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
    use crate::transaction_manager::interface::{
        Database, Decision, Environment, ResourceManager, Unavailable, Vote,
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
    }

    fn environment(resource_managers: Vec<TestResourceManager>) -> TestEnvironment {
        TestEnvironment {
            database_available: true,
            other_handler: None,
            decision: Mutex::default(),
            resource_managers,
        }
    }

    impl TestEnvironment {
        fn received(&self) -> Vec<String> {
            self.resource_managers
                .iter()
                .map(|resource_manager| resource_manager.received.lock().unwrap().join(" "))
                .collect()
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
    }

    #[tokio::test]
    async fn aborts_when_one_is_unavailable() {
        let environment = environment(vec![
            resource_manager(Ok(Vote::Prepared)),
            resource_manager(Err(Unavailable)),
        ]);
        assert_eq!(handle(&environment, "t").await, Ok(Decision::Aborted));
        assert_eq!(environment.received(), ["prepare abort", "prepare abort"]);
    }

    #[tokio::test]
    async fn repeats_a_decision_already_made() {
        let environment = TestEnvironment {
            other_handler: Some(OtherHandler::DecidesBeforeRead(Decision::Committed)),
            ..environment(vec![resource_manager(Ok(Vote::Prepared))])
        };
        assert_eq!(handle(&environment, "t").await, Ok(Decision::Committed));
        assert_eq!(environment.received(), ["commit"]);
    }

    #[tokio::test]
    async fn follows_the_decision_that_stands() {
        let environment = TestEnvironment {
            other_handler: Some(OtherHandler::DecidesBeforeWrite(Decision::Aborted)),
            ..environment(vec![resource_manager(Ok(Vote::Prepared))])
        };
        assert_eq!(handle(&environment, "t").await, Ok(Decision::Aborted));
        assert_eq!(environment.received(), ["prepare abort"]);
    }

    #[tokio::test]
    async fn is_unavailable_without_the_database() {
        let environment = TestEnvironment {
            database_available: false,
            ..environment(vec![resource_manager(Ok(Vote::Prepared))])
        };
        assert_eq!(handle(&environment, "t").await, Err(Unavailable));
        assert_eq!(environment.received(), [""]);
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
