use crate::Error;
use derivative::Derivative;
use parking_lot::RwLock;
use std::collections::BTreeMap;
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

    pub fn empty() -> Self {
        PackedLeaf {
            hash: RwLock::new(Hash256::zero()),
            values: Vec::with_capacity(T::tree_hash_packing_factor()),
        }
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
        let mut updated = PackedLeaf {
            hash: RwLock::new(Hash256::zero()),
            values: self.values.clone(),
        };
        let sub_index = index % T::tree_hash_packing_factor();
        updated.insert_mut(sub_index, value)?;
        Ok(updated)
    }

    pub fn update(
        &self,
        prefix: usize,
        hash: Hash256,
        updates: &BTreeMap<usize, T>,
    ) -> Result<Self, Error> {
        let mut updated = PackedLeaf {
            hash: RwLock::new(hash),
            values: self.values.clone(),
        };

        let packing_factor = T::tree_hash_packing_factor();
        let start = prefix;
        let end = prefix + packing_factor;
        for (index, value) in updates.range(start..end) {
            updated.insert_mut(index % packing_factor, value.clone())?;
        }
        Ok(updated)
    }

    pub fn insert_mut(&mut self, sub_index: usize, value: T) -> Result<(), Error> {
        // Ensure hash is 0.
        *self.hash.get_mut() = Hash256::zero();

        if sub_index == self.values.len() {
            self.values.push(value);
        } else if sub_index < self.values.len() {
            self.values[sub_index] = value;
        } else {
            return Err(Error::Oops);
        }
        Ok(())
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
