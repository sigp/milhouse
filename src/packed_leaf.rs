use crate::{Error, UpdateMap, Value};
use arbitrary::Arbitrary;
use core::marker::PhantomData;
use derivative::Derivative;
use std::ops::ControlFlow;
use tree_hash::{Hash256, BYTES_PER_CHUNK};

/// `Hash256` type which is aligned to a 16-byte boundary.
///
/// This allows pointers to types with alignment 1, 2, 4, 8, 16 to be constructed pointing
/// *into* an `AlignedHash256`.
///
/// In future this could be aligned to a 32-byte boundary, although that would blow out the size
/// of `PackedLeaf` and `Tree`.
#[derive(Clone, Copy, Debug, PartialEq, Hash, Arbitrary)]
#[repr(align(16))]
pub struct AlignedHash256(Hash256);

#[derive(Debug, Derivative, Arbitrary)]
#[derivative(PartialEq, Hash)]
pub struct PackedLeaf<T: Value> {
    pub hash: AlignedHash256,
    pub length: u8,
    _phantom: PhantomData<T>,
}

impl<T> Clone for PackedLeaf<T>
where
    T: Value,
{
    fn clone(&self) -> Self {
        Self {
            hash: self.hash,
            length: self.length,
            _phantom: PhantomData,
        }
    }
}

impl<T: Value> PackedLeaf<T> {
    pub fn length(&self) -> usize {
        self.length as usize
    }

    fn value_len() -> usize {
        BYTES_PER_CHUNK / T::tree_hash_packing_factor()
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.length() {
            return None;
        }
        let hash_base_ptr: *const AlignedHash256 = &self.hash;
        let base_ptr: *const T = hash_base_ptr as *const T;
        let elem_ptr: *const T = unsafe { base_ptr.add(index) };
        Some(unsafe { &*elem_ptr })
    }

    pub fn tree_hash(&self) -> Hash256 {
        self.hash.0
    }

    pub fn empty() -> Self {
        PackedLeaf {
            hash: AlignedHash256(Hash256::zero()),
            length: 0,
            _phantom: PhantomData,
        }
    }

    pub fn single(value: T) -> Self {
        let mut hash = Hash256::zero();
        let hash_bytes = hash.as_bytes_mut();

        let value_len = Self::value_len();
        hash_bytes[0..value_len].copy_from_slice(&value.as_ssz_bytes());

        PackedLeaf {
            hash: AlignedHash256(hash),
            length: 1,
            _phantom: PhantomData,
        }
    }

    pub fn repeat(value: T, n: usize) -> Self {
        assert!(n <= T::tree_hash_packing_factor());

        let mut hash = Hash256::zero();
        let hash_bytes = hash.as_bytes_mut();

        let value_len = Self::value_len();

        for (i, value) in vec![value; n].iter().enumerate() {
            hash_bytes[i * value_len..(i + 1) * value_len].copy_from_slice(&value.as_ssz_bytes());
        }

        PackedLeaf {
            hash: AlignedHash256(hash),
            length: n as u8,
            _phantom: PhantomData,
        }
    }

    pub fn insert_at_index(&self, index: usize, value: T) -> Result<Self, Error> {
        let mut updated = self.clone();

        updated.insert_mut(index, value)?;

        Ok(updated)
    }

    pub fn update<U: UpdateMap<T>>(&self, prefix: usize, updates: &U) -> Result<Self, Error> {
        let packing_factor = T::tree_hash_packing_factor();
        let start = prefix;
        let end = prefix + packing_factor;

        let mut updated = self.clone();

        updates.for_each_range(start, end, |index, value| {
            ControlFlow::Continue(updated.insert_mut(index % packing_factor, value.clone()))
        })?;

        Ok(updated)
    }

    pub fn insert_mut(&mut self, index: usize, value: T) -> Result<(), Error> {
        // Convert the index to the index of the underlying bytes.
        let sub_index = index * Self::value_len();

        if sub_index >= BYTES_PER_CHUNK {
            return Err(Error::PackedLeafOutOfBounds {
                sub_index,
                len: self.length(),
            });
        }

        let value_len = Self::value_len();

        let mut hash = self.hash;
        let hash_bytes = hash.0.as_bytes_mut();

        hash_bytes[sub_index..sub_index + value_len].copy_from_slice(&value.as_ssz_bytes());

        self.hash = hash;

        if index == self.length() {
            self.length += 1;
        } else if index > self.length() {
            return Err(Error::PackedLeafOutOfBounds {
                sub_index,
                len: self.length(),
            });
        }

        Ok(())
    }

    pub fn push(&mut self, value: T) -> Result<(), Error> {
        // Ensure a new T will not overflow the leaf.
        if self.length() >= T::tree_hash_packing_factor() {
            return Err(Error::PackedLeafFull { len: self.length() });
        }

        self.insert_mut(self.length(), value)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn align_of_aligned_hash256() {
        assert_eq!(std::mem::align_of::<AlignedHash256>(), 16);
    }
}
