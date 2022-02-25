use std::collections::BTreeMap;
use tree_hash::{Hash256, TreeHash, TreeHashType};

/// Length type, to avoid confusion with depth and other `usize` parameters.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct Length(pub usize);

impl Length {
    pub fn as_mut(&mut self) -> &mut usize {
        &mut self.0
    }

    pub fn as_usize(&self) -> usize {
        self.0
    }
}

/// Compute ceil(log(n))
///
/// Smallest number of bits d so that n <= 2^d
pub fn int_log(n: usize) -> usize {
    match n.checked_next_power_of_two() {
        Some(x) => x.trailing_zeros() as usize,
        None => 8 * std::mem::size_of::<usize>(),
    }
}

pub fn opt_packing_factor<T: TreeHash>() -> Option<usize> {
    match T::tree_hash_type() {
        TreeHashType::Basic => Some(T::tree_hash_packing_factor()),
        TreeHashType::Container | TreeHashType::List | TreeHashType::Vector => None,
    }
}

/// Compute the depth in a tree at which to start packing values into a `PackedLeaf`.
pub fn opt_packing_depth<T: TreeHash>() -> Option<usize> {
    let packing_factor = opt_packing_factor::<T>()?;
    Some(int_log(packing_factor))
}

/// Compute the maximum index of a BTreeMap.
pub fn max_btree_index<T>(map: &BTreeMap<usize, T>) -> Option<usize> {
    map.keys().next_back().copied()
}

/// Compute the length a data structure will have after applying `updates`.
pub fn updated_length<T>(prev_len: Length, updates: &BTreeMap<usize, T>) -> Length {
    max_btree_index(updates).map_or(prev_len, |max_idx| {
        Length(std::cmp::max(max_idx + 1, prev_len.as_usize()))
    })
}

/// Get the hash of a node at `(depth, prefix)` from an optional HashMap.
pub fn opt_hash(
    hashes: Option<&BTreeMap<(usize, usize), Hash256>>,
    depth: usize,
    prefix: usize,
) -> Option<Hash256> {
    hashes?.get(&(depth, prefix)).copied()
}
