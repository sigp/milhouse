use crate::{
    utils::{arb_arc, arb_rwlock},
    Arc,
};
use arbitrary::Arbitrary;
use educe::Educe;
use parking_lot::RwLock;
use tree_hash::Hash256;

#[derive(Debug, Educe, Arbitrary)]
#[educe(PartialEq, Hash)]
pub struct Leaf<T> {
    #[educe(PartialEq(ignore), Hash(ignore))]
    #[arbitrary(with = arb_rwlock)]
    pub hash: RwLock<Hash256>,
    #[arbitrary(with = arb_arc)]
    pub value: Arc<T>,
}

impl<T> Clone for Leaf<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            hash: RwLock::new(*self.hash.read()),
            value: self.value.clone(),
        }
    }
}

impl<T> Leaf<T> {
    pub fn new(value: T) -> Self {
        Self::with_hash(value, Hash256::ZERO)
    }

    pub fn with_hash(value: T, hash: Hash256) -> Self {
        Self {
            hash: RwLock::new(hash),
            value: Arc::new(value),
        }
    }
}
