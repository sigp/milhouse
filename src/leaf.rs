use crate::Arc;
use educe::Educe;
use parking_lot::RwLock;
use tree_hash::Hash256;

#[derive(Debug, Educe)]
#[cfg_attr(feature = "arbitrary", derive(arbitrary::Arbitrary))]
#[educe(PartialEq, Hash)]
pub struct Leaf<T> {
    #[educe(PartialEq(ignore), Hash(ignore))]
    #[cfg_attr(feature = "arbitrary", arbitrary(with = crate::utils::arb_rwlock))]
    pub hash: RwLock<Hash256>,
    #[cfg_attr(feature = "arbitrary", arbitrary(with = crate::utils::arb_arc))]
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
