use std::collections::BTreeMap;
use tree_hash::{TreeHash, TreeHashType};

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
pub fn updated_length<T>(prev_len: usize, updates: &BTreeMap<usize, T>) -> usize {
    max_btree_index(updates).map_or(prev_len, |max_idx| std::cmp::max(max_idx + 1, prev_len))
}
