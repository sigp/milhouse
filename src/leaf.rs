use crate::{
    utils::{arb_arc, arb_rwlock},
    Arc,
};
use arbitrary::Arbitrary;
use derivative::Derivative;
use tokio::sync::RwLock;
use tree_hash::Hash256;

#[derive(Debug, Derivative, Arbitrary)]
#[derivative(PartialEq, Hash)]
pub struct Leaf<T> {
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    #[arbitrary(with = arb_rwlock)]
    pub hash: RwLock<Hash256>,
    #[arbitrary(with = arb_arc)]
    pub value: Arc<T>,
}

impl<T> Leaf<T> {
    pub fn new(value: T) -> Self {
        Self::with_hash(value, Hash256::zero())
    }

    pub fn with_hash(value: T, hash: Hash256) -> Self {
        Self {
            hash: RwLock::new(hash),
            value: Arc::new(value),
        }
    }
}
