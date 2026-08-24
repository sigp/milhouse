//! Lock-free write-once hash cache for tree hash values.
//!
//! `HashCell` caches a single `Hash256` using atomics instead of a lock. Reads are
//! non-blocking (`Acquire` load on a bool + four `Relaxed` loads), and `set()`
//! skips the write if the cell is already initialized.
//!
//! ## Memory ordering
//!
//! The first writer does a `Release` store on `ready`, which synchronizes-with the
//! `Acquire` load in `get()`. Subsequent `set()` calls observe `true` and return
//! early without writing.
//!
//! ## Safety invariant
//!
//! All callers must write the same value for a given cell. This is guaranteed by
//! tree hash. All threads compute the same hash for the same tree node.

use std::fmt;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use tree_hash::Hash256;

/// Lock-free write-once hash cache.
pub struct HashCell {
    /// Whether the cell has been initialized with a hash value.
    ready: AtomicBool,
    /// The cached Hash256 hash value, stored as 4 × AtomicU64 for lock-free
    /// unconditional writes without data races.
    value: [AtomicU64; 4],
}

impl HashCell {
    /// Create a new empty (uninitialized) hash cell.
    pub const fn new() -> Self {
        HashCell {
            ready: AtomicBool::new(false),
            value: [
                AtomicU64::new(0),
                AtomicU64::new(0),
                AtomicU64::new(0),
                AtomicU64::new(0),
            ],
        }
    }

    /// Read the cached hash value, if initialized.
    ///
    /// Returns `None` if the cell has not been initialized.
    /// Returns `Some(hash)` if at least one writer has completed `set()`.
    #[inline]
    pub fn get(&self) -> Option<Hash256> {
        if !self.ready.load(Ordering::Acquire) {
            return None;
        }
        // The Acquire load above synchronizes-with the Release store in `set()`,
        // guaranteeing that all Relaxed stores to `value` by the first writer are
        // visible. Redundant writers store the same bytes, so concurrent reads
        // always produce the correct hash.
        Some(self.load_value())
    }

    /// Write the hash value if the cell is uninitialized.
    ///
    /// If another thread has already initialized this cell, the write is skipped.
    #[inline]
    pub fn set(&self, hash: Hash256) {
        if self.ready.load(Ordering::Acquire) {
            #[cfg(debug_assertions)]
            debug_assert_eq!(
                self.load_value(),
                hash,
                "HashCell written with different value"
            );
            return;
        }
        self.store_value(hash);
        self.ready.store(true, Ordering::Release);
    }

    /// Reset the cell to the uninitialized state.
    /// This avoids constructing a new HashCell and the stale value will never
    /// be read.
    #[inline]
    pub fn clear(&mut self) {
        *self.ready.get_mut() = false;
    }

    /// Load the cached Hash256 from the four AtomicU64 parts.
    #[inline(always)]
    fn load_value(&self) -> Hash256 {
        let mut bytes = [0u8; 32];
        for i in 0..4 {
            let val = self.value[i].load(Ordering::Relaxed);
            bytes[i * 8..][..8].copy_from_slice(&val.to_le_bytes());
        }
        Hash256::new(bytes)
    }

    /// Store Hash256 into the four AtomicU64 parts.
    #[inline(always)]
    fn store_value(&self, hash: Hash256) {
        let bytes = hash.0;
        for i in 0..4 {
            let mut buf = [0u8; 8];
            buf.copy_from_slice(&bytes[i * 8..][..8]);
            self.value[i].store(u64::from_le_bytes(buf), Ordering::Relaxed);
        }
    }
}

impl Default for HashCell {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for HashCell {
    fn clone(&self) -> Self {
        match self.get() {
            Some(h) => Self::from(h),
            None => Self::new(),
        }
    }
}

impl From<Hash256> for HashCell {
    fn from(hash: Hash256) -> Self {
        let cell = Self::new();
        cell.set(hash);
        cell
    }
}

impl From<Option<Hash256>> for HashCell {
    fn from(hash: Option<Hash256>) -> Self {
        match hash {
            Some(h) => Self::from(h),
            None => Self::new(),
        }
    }
}

impl fmt::Debug for HashCell {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.get() {
            Some(h) => f.debug_tuple("HashCell").field(&h).finish(),
            None => write!(f, "HashCell(<empty>)"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_cell_is_empty() {
        let cell = HashCell::new();
        assert!(cell.get().is_none());
    }

    #[test]
    fn set_then_get() {
        let cell = HashCell::new();
        let hash = Hash256::from([0xAB; 32]);
        cell.set(hash);
        assert_eq!(cell.get(), Some(hash));
    }

    #[test]
    fn from_value() {
        let hash = Hash256::from([0xCD; 32]);
        let cell = HashCell::from(hash);
        assert_eq!(cell.get(), Some(hash));
    }

    #[test]
    fn zero_hash_is_cached_correctly() {
        let cell = HashCell::new();
        cell.set(Hash256::ZERO);
        assert_eq!(cell.get(), Some(Hash256::ZERO));
    }

    #[test]
    fn redundant_set_preserves_value() {
        let cell = HashCell::new();
        let hash = Hash256::from([0x42; 32]);
        cell.set(hash);
        // Redundant set with the same value.
        cell.set(hash);
        assert_eq!(cell.get(), Some(hash));
    }

    #[test]
    fn clone_preserves_value() {
        let cell = HashCell::from(Hash256::from([0x11; 32]));
        let cloned = cell.clone();
        assert_eq!(cloned.get(), cell.get());
    }

    #[test]
    fn clone_empty_is_empty() {
        let cell = HashCell::new();
        let cloned = cell.clone();
        assert!(cloned.get().is_none());
    }

    #[test]
    fn size_and_alignment() {
        assert_eq!(size_of::<HashCell>(), 40);
        assert_eq!(align_of::<HashCell>(), 8);
    }

    #[test]
    fn concurrent_set_same_value() {
        use std::sync::Arc;
        let cell = Arc::new(HashCell::new());
        let hash = Hash256::from([0xFF; 32]);

        let handles: Vec<_> = (0..8)
            .map(|_| {
                let cell = cell.clone();
                std::thread::spawn(move || {
                    cell.set(hash);
                })
            })
            .collect();

        for h in handles {
            h.join().expect("thread panicked");
        }

        assert_eq!(cell.get(), Some(hash));
    }

    #[test]
    fn concurrent_get_and_set() {
        use std::sync::Arc;
        let cell = Arc::new(HashCell::new());
        let hash = Hash256::from([0xEE; 32]);

        let handles: Vec<_> = (0..8)
            .map(|i| {
                let cell = cell.clone();
                if i % 2 == 0 {
                    std::thread::spawn(move || {
                        cell.set(hash);
                    })
                } else {
                    std::thread::spawn(move || {
                        // Reader may see None or Some(hash), never anything else.
                        if let Some(v) = cell.get() {
                            assert_eq!(v, hash);
                        }
                    })
                }
            })
            .collect();

        for h in handles {
            h.join().expect("thread panicked");
        }

        assert_eq!(cell.get(), Some(hash));
    }

    #[test]
    fn from_option_some() {
        let hash = Hash256::from([0xBB; 32]);
        let cell = HashCell::from(Some(hash));
        assert_eq!(cell.get(), Some(hash));
    }

    #[test]
    fn from_option_none() {
        let cell = HashCell::from(None);
        assert!(cell.get().is_none());
    }

    #[test]
    fn clear_resets_initialized_cell() {
        let mut cell = HashCell::from(Hash256::from([0xAA; 32]));
        assert!(cell.get().is_some());
        cell.clear();
        assert!(cell.get().is_none());
    }

    #[test]
    fn clear_on_empty_is_noop() {
        let mut cell = HashCell::new();
        assert!(cell.get().is_none());
        cell.clear();
        assert!(cell.get().is_none());
    }

    #[test]
    fn set_after_clear() {
        let mut cell = HashCell::from(Hash256::from([0xAA; 32]));
        cell.clear();
        let new_hash = Hash256::from([0xBB; 32]);
        cell.set(new_hash);
        assert_eq!(cell.get(), Some(new_hash));
    }
}
