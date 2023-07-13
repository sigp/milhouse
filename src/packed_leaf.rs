use crate::{utils::arb_rwlock, Error, UpdateMap, Value};
use arbitrary::Arbitrary;
use core::marker::PhantomData;
use derivative::Derivative;
use parking_lot::RwLock;
use std::ops::ControlFlow;
use tree_hash::{Hash256, BYTES_PER_CHUNK};

#[derive(Debug, Derivative, Arbitrary)]
#[derivative(PartialEq, Hash)]
pub struct PackedLeaf<T: Value> {
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    #[arbitrary(with = arb_rwlock)]
    pub hash: RwLock<Hash256>,
    pub length: u8,
    _phantom: PhantomData<T>,
}

impl<T> Clone for PackedLeaf<T>
where
    T: Value,
{
    fn clone(&self) -> Self {
        Self {
            hash: RwLock::new(*self.hash.read()),
            length: self.length,
            _phantom: PhantomData,
        }
    }
}

impl<T: Value> PackedLeaf<T> {
    fn length(&self) -> usize {
        self.length as usize
    }

    fn value_len(_value: &T) -> usize {
        BYTES_PER_CHUNK / T::tree_hash_packing_factor()
    }

    pub fn values(&self) -> Vec<T> {
        self.hash
            .read()
            .as_bytes()
            .chunks_exact(BYTES_PER_CHUNK / T::tree_hash_packing_factor())
            .take(self.length())
            .map(|bytes| T::from_ssz_bytes(bytes).expect("Should always deserialize"))
            .collect::<Vec<T>>()
    }

    pub fn get(&self, index: usize) -> Option<T> {
        self.values().get(index).cloned()
    }

    pub fn tree_hash(&self) -> Hash256 {
        *self.hash.read()
    }

    pub fn empty() -> Self {
        PackedLeaf {
            hash: RwLock::new(Hash256::zero()),
            length: 0,
            _phantom: PhantomData,
        }
    }

    pub fn single(value: T) -> Self {
        let mut hash = Hash256::zero();
        let hash_bytes = hash.as_bytes_mut();

        let value_len = Self::value_len(&value);
        hash_bytes[0..value_len].copy_from_slice(&value.as_ssz_bytes());

        PackedLeaf {
            hash: RwLock::new(hash),
            length: 1,
            _phantom: PhantomData,
        }
    }

    pub fn repeat(value: T, n: usize) -> Self {
        assert!(n <= T::tree_hash_packing_factor());

        let mut hash = Hash256::zero();
        let hash_bytes = hash.as_bytes_mut();

        let value_len = Self::value_len(&value);

        for (i, value) in vec![value; n].iter().enumerate() {
            hash_bytes[i * value_len..(i + 1) * value_len].copy_from_slice(&value.as_ssz_bytes());
        }

        PackedLeaf {
            hash: RwLock::new(hash),
            length: n as u8,
            _phantom: PhantomData,
        }
    }

    pub fn insert_at_index(&self, index: usize, value: T) -> Result<Self, Error> {
        let mut updated = self.clone();

        updated.insert_mut(index, value)?;

        Ok(updated)
    }

    pub fn update<U: UpdateMap<T>>(
        &self,
        prefix: usize,
        _hash: Hash256,
        updates: &U,
    ) -> Result<Self, Error> {
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
        let sub_index = index * Self::value_len(&value);

        if sub_index >= BYTES_PER_CHUNK {
            return Err(Error::PackedLeafOutOfBounds {
                sub_index,
                len: self.length(),
            });
        }

        let value_len = Self::value_len(&value);

        let mut hash = *self.hash.read();
        let hash_bytes = hash.as_bytes_mut();

        hash_bytes[sub_index..sub_index + value_len].copy_from_slice(&value.as_ssz_bytes());

        *self.hash.write() = hash;

        if index == self.length() {
            self.length += 1;
        } else if index > self.length() {
            panic!("This is bad");
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
