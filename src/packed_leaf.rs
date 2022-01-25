use crate::Error;
use derivative::Derivative;
use parking_lot::RwLock;
use smallvec::{smallvec, SmallVec};
use tree_hash::{Hash256, TreeHash, BYTES_PER_CHUNK};

pub const MAX_FACTOR: usize = 32;

#[derive(Debug, Derivative)]
#[derivative(PartialEq, Hash)]
pub struct PackedLeaf<T: TreeHash + Clone> {
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    pub hash: RwLock<Option<Hash256>>,
    pub(crate) values: SmallVec<[T; MAX_FACTOR]>,
}

impl<T> Clone for PackedLeaf<T>
where
    T: TreeHash + Clone,
{
    fn clone(&self) -> Self {
        Self {
            hash: RwLock::new(self.hash.read().as_ref().cloned()),
            values: self.values.clone(),
        }
    }
}

impl<T: TreeHash + Clone> PackedLeaf<T> {
    pub fn tree_hash(&self) -> Hash256 {
        let read_lock = self.hash.read();
        let existing_hash = *read_lock;
        drop(read_lock);

        if let Some(hash) = existing_hash {
            return hash;
        }

        let mut hash = Hash256::zero();
        let hash_bytes = hash.as_bytes_mut();

        let value_len = BYTES_PER_CHUNK / T::tree_hash_packing_factor();
        for (i, value) in self.values.iter().enumerate() {
            hash_bytes[i * value_len..(i + 1) * value_len]
                .copy_from_slice(&value.tree_hash_packed_encoding());
        }

        *self.hash.write() = Some(hash);
        hash
    }

    pub fn single(value: T) -> Self {
        PackedLeaf {
            hash: RwLock::new(None),
            values: smallvec![value],
        }
    }

    pub fn insert_at_index(&self, index: usize, value: T) -> Result<Self, Error> {
        let sub_index = index % T::tree_hash_packing_factor();

        let mut values = self.values.clone();

        if sub_index == self.values.len() {
            values.push(value);
        } else if sub_index < self.values.len() {
            values[sub_index] = value;
        } else {
            return Err(Error::Oops);
        }

        Ok(Self {
            hash: RwLock::new(None),
            values,
        })
    }
}
