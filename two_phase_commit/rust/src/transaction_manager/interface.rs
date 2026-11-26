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
