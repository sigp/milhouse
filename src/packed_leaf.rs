use crate::Error;
use derivative::Derivative;
use parking_lot::RwLock;
use tree_hash::{Hash256, TreeHash, BYTES_PER_CHUNK};

#[derive(Debug, Derivative)]
#[derivative(PartialEq, Hash)]
pub struct PackedLeaf<T: TreeHash + Clone> {
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    pub hash: RwLock<Hash256>,
    pub(crate) values: Vec<T>,
}

impl<T> Clone for PackedLeaf<T>
where
    T: TreeHash + Clone,
{
    fn clone(&self) -> Self {
        Self {
            hash: RwLock::new(*self.hash.read()),
            values: self.values.clone(),
        }
    }
}

impl<T: TreeHash + Clone> PackedLeaf<T> {
    pub fn tree_hash(&self) -> Hash256 {
        let read_lock = self.hash.read();
        let mut hash = *read_lock;
        drop(read_lock);

        if !hash.is_zero() {
            return hash;
        }

        let hash_bytes = hash.as_bytes_mut();

        let value_len = BYTES_PER_CHUNK / T::tree_hash_packing_factor();
        for (i, value) in self.values.iter().enumerate() {
            hash_bytes[i * value_len..(i + 1) * value_len]
                .copy_from_slice(&value.tree_hash_packed_encoding());
        }

        *self.hash.write() = hash;
        hash
    }

    pub fn single(value: T) -> Self {
        let mut values = Vec::with_capacity(T::tree_hash_packing_factor());
        values.push(value);

        PackedLeaf {
            hash: RwLock::new(Hash256::zero()),
            values,
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
            hash: RwLock::new(Hash256::zero()),
            values,
        })
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        if self.values.len() == T::tree_hash_packing_factor() {
            return Err(Error::PackedLeafFull {
                len: self.values.len(),
            });
        }
        self.values.push(value);
        Ok(())
    }
}
