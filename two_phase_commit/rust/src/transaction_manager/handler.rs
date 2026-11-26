use std::time::Duration;

use super::interface::{Decision, Environment, ResourceManager, Unavailable, Vote};

const TIMEOUT: Duration = Duration::from_secs(1);

pub async fn handle(
    environment: &impl Environment,
    transaction_id: &str,
) -> Result<Decision, Unavailable> {
    let decision = match environment.read_decision(transaction_id).await? {
        Some(decision) => decision,
        None => {
            let mut proposal = Decision::Committed;
            for resource_manager in environment.resource_managers() {
                match resource_manager.prepare(transaction_id, TIMEOUT).await {
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

    let mut outcome = Ok(decision);
    for resource_manager in environment.resource_managers() {
        let informed = match decision {
            Decision::Committed => resource_manager.commit(transaction_id).await,
            Decision::Aborted => resource_manager.abort(transaction_id).await,
        };
        if informed.is_err() {
            outcome = Err(Unavailable);
        }
    }
    outcome
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;
    use std::time::Duration;

    use super::handle;
    use crate::transaction_manager::interface::{
        Database, Decision, Environment, ResourceManager, Unavailable, Vote,
    };

    struct TestResourceManager {
        vote: Result<Vote, Unavailable>,
        informed: Result<(), Unavailable>,
        received: Mutex<Vec<&'static str>>,
    }

    fn resource_manager(vote: Result<Vote, Unavailable>) -> TestResourceManager {
        TestResourceManager {
            vote,
            informed: Ok(()),
            received: Mutex::default(),
        }
    }

    impl ResourceManager for TestResourceManager {
        async fn prepare(&self, _: &str, _: Duration) -> Result<Vote, Unavailable> {
            self.received.lock().unwrap().push("prepare");
            self.vote
        }

        async fn commit(&self, _: &str) -> Result<(), Unavailable> {
            self.received.lock().unwrap().push("commit");
            self.informed
        }

        async fn abort(&self, _: &str) -> Result<(), Unavailable> {
            self.received.lock().unwrap().push("abort");
            self.informed
        }
    }

    struct TestEnvironment {
        database_available: bool,
        decision: Mutex<Option<Decision>>,
        written_concurrently: Option<Decision>,
        resource_managers: Vec<TestResourceManager>,
    }

    fn environment(resource_managers: Vec<TestResourceManager>) -> TestEnvironment {
        TestEnvironment {
            database_available: true,
            decision: Mutex::default(),
            written_concurrently: None,
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
            Ok(*self.decision.lock().unwrap())
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
            Ok(*stored.get_or_insert(self.written_concurrently.unwrap_or(decision)))
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

    #[tokio::test]
    async fn aborts_as_soon_as_one_refuses() {
        let environment = environment(vec![
            resource_manager(Ok(Vote::Prepared)),
            resource_manager(Ok(Vote::Refused)),
            resource_manager(Ok(Vote::Prepared)),
        ]);
        assert_eq!(handle(&environment, "t").await, Ok(Decision::Aborted));
        assert_eq!(
            environment.received(),
            ["prepare abort", "prepare abort", "abort"]
        );
    }

    #[tokio::test]
    async fn aborts_when_one_is_unavailable() {
        let environment = environment(vec![
            resource_manager(Err(Unavailable)),
            resource_manager(Ok(Vote::Prepared)),
        ]);
        assert_eq!(handle(&environment, "t").await, Ok(Decision::Aborted));
        assert_eq!(environment.received(), ["prepare abort", "abort"]);
    }

    #[tokio::test]
    async fn repeats_a_decision_already_made() {
        let environment = TestEnvironment {
            decision: Mutex::new(Some(Decision::Committed)),
            ..environment(vec![resource_manager(Ok(Vote::Prepared))])
        };
        assert_eq!(handle(&environment, "t").await, Ok(Decision::Committed));
        assert_eq!(environment.received(), ["commit"]);
    }

    #[tokio::test]
    async fn follows_the_decision_that_stands() {
        let environment = TestEnvironment {
            written_concurrently: Some(Decision::Aborted),
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
                informed: Err(Unavailable),
                ..resource_manager(Ok(Vote::Prepared))
            },
            resource_manager(Ok(Vote::Prepared)),
        ]);
        assert_eq!(handle(&environment, "t").await, Err(Unavailable));
        assert_eq!(environment.received(), ["prepare commit", "prepare commit"]);
    }

    #[test]
    fn handle_is_send() {
        fn is_send(_: impl Send) {}
        is_send(handle(&environment(vec![]), "t"));
    }
}
