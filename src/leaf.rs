use derivative::Derivative;
use parking_lot::RwLock;
use tree_hash::Hash256;

#[derive(Debug, Derivative)]
#[derivative(PartialEq)]
pub struct Leaf<T> {
    #[derivative(PartialEq = "ignore")]
    pub hash: RwLock<Option<Hash256>>,
    pub value: T,
}

impl<T> Clone for Leaf<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            hash: RwLock::new(self.hash.read().as_ref().cloned()),
            value: self.value.clone(),
        }
    }
}

impl<T> Leaf<T> {
    pub fn new(value: T) -> Self {
        Self {
            hash: RwLock::new(None),
            value,
        }
    }
}
