use crate::{Error, UpdateMap};
use arbitrary::Arbitrary;
use derivative::Derivative;
use std::ops::ControlFlow;
use tree_hash::{Hash256, TreeHash, BYTES_PER_CHUNK};

#[derive(Debug, Derivative, Arbitrary)]
#[derivative(PartialEq, Hash)]
pub struct PackedLeaf<T: TreeHash + Clone> {
    pub(crate) values: Vec<T>,
}

impl<T> Clone for PackedLeaf<T>
where
    T: TreeHash + Clone,
{
    fn clone(&self) -> Self {
        Self {
            values: self.values.clone(),
        }
    }
}

impl<T: TreeHash + Clone> PackedLeaf<T> {
    pub fn tree_hash(&self) -> Hash256 {
        //let read_lock = self.hash.read();
        //let mut hash = *read_lock;
        //drop(read_lock);

        //if !hash.is_zero() {
        //    return hash;
        //}

        let mut hash = Hash256::zero();

        let hash_bytes = hash.as_bytes_mut();

        let value_len = BYTES_PER_CHUNK / T::tree_hash_packing_factor();
        for (i, value) in self.values.iter().enumerate() {
            hash_bytes[i * value_len..(i + 1) * value_len]
                .copy_from_slice(&value.tree_hash_packed_encoding());
        }

        hash
    }

    pub fn empty() -> Self {
        PackedLeaf {
            values: Vec::with_capacity(T::tree_hash_packing_factor()),
        }
    }

    pub fn single(value: T) -> Self {
        let mut values = Vec::with_capacity(T::tree_hash_packing_factor());
        values.push(value);

        PackedLeaf { values }
    }

    pub fn repeat(value: T, n: usize) -> Self {
        assert!(n <= T::tree_hash_packing_factor());
        PackedLeaf {
            values: vec![value; n],
        }
    }

    pub fn insert_at_index(&self, index: usize, value: T) -> Result<Self, Error> {
        let mut updated = PackedLeaf {
            values: self.values.clone(),
        };
        let sub_index = index % T::tree_hash_packing_factor();
        updated.insert_mut(sub_index, value)?;
        Ok(updated)
    }

    pub fn update<U: UpdateMap<T>>(&self, prefix: usize, updates: &U) -> Result<Self, Error> {
        let mut updated = PackedLeaf {
            values: self.values.clone(),
        };

        let packing_factor = T::tree_hash_packing_factor();
        let start = prefix;
        let end = prefix + packing_factor;
        updates.for_each_range(start, end, |index, value| {
            ControlFlow::Continue(updated.insert_mut(index % packing_factor, value.clone()))
        })?;
        Ok(updated)
    }

    pub fn insert_mut(&mut self, sub_index: usize, value: T) -> Result<(), Error> {
        // Ensure hash is 0.
        //*self.hash.get_mut() = Hash256::zero();
        // TODO(mac) might need another check here

        if sub_index == self.values.len() {
            self.values.push(value);
        } else if sub_index < self.values.len() {
            self.values[sub_index] = value;
        } else {
            return Err(Error::PackedLeafOutOfBounds {
                sub_index,
                len: self.values.len(),
            });
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
