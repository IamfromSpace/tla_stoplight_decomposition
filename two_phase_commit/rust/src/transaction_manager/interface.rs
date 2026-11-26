#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Vote {
    Prepared,
    Refused,
}

pub trait ResourceManager: Sync {
    /// Never returns two different votes for the same transaction.
    fn prepare(&self, transaction_id: &str) -> impl Future<Output = Option<Vote>> + Send;
    fn commit(&self, transaction_id: &str) -> impl Future<Output = ()> + Send;
    fn abort(&self, transaction_id: &str) -> impl Future<Output = ()> + Send;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision {
    Committed,
    Aborted,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unavailable;

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
