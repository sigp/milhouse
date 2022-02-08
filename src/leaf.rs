use derivative::Derivative;
use parking_lot::RwLock;
use tree_hash::Hash256;
use triomphe::Arc;

#[derive(Debug, Derivative)]
#[derivative(PartialEq, Hash)]
pub struct Leaf<T> {
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    pub hash: RwLock<Hash256>,
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
        Self {
            hash: RwLock::new(Hash256::zero()),
            value: Arc::new(value),
        }
    }
}
