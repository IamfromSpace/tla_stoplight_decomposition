use std::time::Duration;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unavailable;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Vote {
    Prepared,
    Refused,
}

pub trait ResourceManager: Sync {
    /// Never returns two different votes for the same transaction.
    fn prepare(
        &self,
        transaction_id: &str,
        timeout: Duration,
    ) -> impl Future<Output = Result<Vote, Unavailable>> + Send;
    fn commit(&self, transaction_id: &str) -> impl Future<Output = Result<(), Unavailable>> + Send;
    fn abort(&self, transaction_id: &str) -> impl Future<Output = Result<(), Unavailable>> + Send;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Decision {
    Committed,
    Aborted,
}

pub trait Database: Sync {
    fn read_decision(
        &self,
        transaction_id: &str,
    ) -> impl Future<Output = Result<Option<Decision>, Unavailable>> + Send;
    /// Only the first decision written for a transaction stands, and it's what this returns.
    fn write_decision(
        &self,
        transaction_id: &str,
        decision: Decision,
    ) -> impl Future<Output = Result<Decision, Unavailable>> + Send;
}

/// A step of two_phase_commit_transaction_manager_handlers.tla, by one handler, with resource
/// managers numbered as in [`Environment::resource_managers`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HandlerStep {
    Start,
    Collect,
    Learn(Decision),
    RequestPrepare(usize),
    ReceivePrepared(usize),
    Commit,
    Abort,
    Timeout,
    Broadcast(usize),
}

pub trait HandlerLog: Sync {
    /// Hears of each step as the handler takes it, so a step that sends a request comes just
    /// before the request does.
    fn record(&self, step: HandlerStep);
}

pub trait Environment: Database {
    type ResourceManager: ResourceManager;
    fn resource_managers(&self) -> &[Self::ResourceManager];
}
