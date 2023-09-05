use crate::{utils::arb_rwlock, Error, UpdateMap};
use arbitrary::Arbitrary;
use derivative::Derivative;
use parking_lot::{RwLock, RwLockUpgradableReadGuard};
use std::ops::ControlFlow;
use tree_hash::{Hash256, TreeHash, BYTES_PER_CHUNK};

#[derive(Debug, Derivative, Arbitrary)]
#[derivative(PartialEq, Hash)]
pub struct PackedLeaf<T: TreeHash + Clone> {
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    #[arbitrary(with = arb_rwlock)]
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
    fn compute_hash(&self, mut hash: Hash256) -> Hash256 {
        let hash_bytes = hash.as_bytes_mut();
        let value_len = BYTES_PER_CHUNK / T::tree_hash_packing_factor();
        for (i, value) in self.values.iter().enumerate() {
            hash_bytes[i * value_len..(i + 1) * value_len]
                .copy_from_slice(&value.tree_hash_packed_encoding());
        }
        hash
    }

    pub fn tree_hash(&self) -> Hash256 {
        let read_lock = self.hash.upgradable_read();
        let hash = *read_lock;

        if !hash.is_zero() {
            hash
        } else {
            match RwLockUpgradableReadGuard::try_upgrade(read_lock) {
                Ok(mut write_lock) => {
                    // If we successfully acquire the lock we are guaranteed to be the first and
                    // only thread attempting to write the hash.
                    let tree_hash = self.compute_hash(hash);

                    *write_lock = tree_hash;
                    tree_hash
                }
                Err(lock) => {
                    // Another thread is holding a lock. Drop the lock and attempt to
                    // acquire a new one. This will avoid a deadlock.
                    RwLockUpgradableReadGuard::unlock_fair(lock);
                    let mut write_lock = self.hash.write();

                    // Since we just acquired the write lock normally, another thread may have
                    // just finished computing the hash. If so, return it.
                    let existing_hash = *write_lock;
                    if !existing_hash.is_zero() {
                        return existing_hash;
                    }

                    let tree_hash = self.compute_hash(hash);

                    *write_lock = tree_hash;
                    tree_hash
                }
            }
        }
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

    pub fn repeat(value: T, n: usize) -> Self {
        assert!(n <= T::tree_hash_packing_factor());
        PackedLeaf {
            hash: RwLock::new(Hash256::zero()),
            values: vec![value; n],
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

    pub fn update<U: UpdateMap<T>>(
        &self,
        prefix: usize,
        hash: Hash256,
        updates: &U,
    ) -> Result<Self, Error> {
        let mut updated = PackedLeaf {
            hash: RwLock::new(hash),
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
        *self.hash.get_mut() = Hash256::zero();

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
