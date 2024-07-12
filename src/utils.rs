use crate::{Arc, UpdateMap};
use arbitrary::Arbitrary;
use arc_swap::ArcSwap;
use parking_lot::RwLock;
use std::collections::BTreeMap;
use tree_hash::{Hash256, TreeHash, TreeHashType};

/// Type to abstract over whether `T` is wrapped in an `Arc` or not.
#[derive(Debug)]
pub enum MaybeArced<T> {
    Arced(Arc<T>),
    Unarced(T),
}

impl<T> MaybeArced<T> {
    pub fn arced(self) -> Arc<T> {
        match self {
            Self::Arced(arc) => arc,
            Self::Unarced(value) => Arc::new(value),
        }
    }
}

/// Length type, to avoid confusion with depth and other `usize` parameters.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Arbitrary)]
pub struct Length(pub usize);

impl Length {
    #[allow(clippy::should_implement_trait)]
    pub fn as_mut(&mut self) -> &mut usize {
        &mut self.0
    }

    #[inline(always)]
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

/// Compute the depth of the largest subtree which has the `index`th element as its 0th leaf.
///
/// A level is fundamentally the same as a depth, it is a value `0..=depth` such that a subtree
/// at that level (depth) contains up to 2^level elements at the leaves. Level 0 is the level of
/// leaves and packed leaves.
pub fn compute_level(index: usize, depth: usize, packing_depth: usize) -> usize {
    let raw_level = if index == 0 {
        depth + packing_depth
    } else {
        index.trailing_zeros() as usize
    };
    if raw_level < packing_depth {
        0
    } else {
        raw_level
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
pub fn updated_length<U: UpdateMap<T>, T>(prev_len: Length, updates: &U) -> Length {
    updates.max_index().map_or(prev_len, |max_idx| {
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

pub fn arb_arc<'a, T: Arbitrary<'a>>(
    u: &mut arbitrary::Unstructured<'a>,
) -> arbitrary::Result<Arc<T>> {
    T::arbitrary(u).map(Arc::new)
}

pub fn arb_rwlock<'a, T: Arbitrary<'a>>(
    u: &mut arbitrary::Unstructured<'a>,
) -> arbitrary::Result<RwLock<T>> {
    T::arbitrary(u).map(RwLock::new)
}

pub fn arb_arc_rwlock<'a, T: Arbitrary<'a>>(
    u: &mut arbitrary::Unstructured<'a>,
) -> arbitrary::Result<std::sync::Arc<RwLock<T>>> {
    T::arbitrary(u).map(RwLock::new).map(std::sync::Arc::new)
}

pub fn arb_arc_swap<'a, T: Arbitrary<'a>>(
    u: &mut arbitrary::Unstructured<'a>,
) -> arbitrary::Result<ArcSwap<T>> {
    T::arbitrary(u).map(std::sync::Arc::new).map(ArcSwap::new)
}

pub fn partial_eq_rwlock<'a, T: PartialEq>(x: &RwLock<T>, y: &RwLock<T>) -> bool {
    *x.read() == *y.read()
}

pub fn partial_eq_arc_swap<'a, T: PartialEq>(x: &ArcSwap<T>, y: &ArcSwap<T>) -> bool {
    *x.load() == *y.load()
}

#[cfg(test)]
mod test {
    use super::*;

    /// The level of an odd index is always 0.
    #[test]
    fn odd_index_level() {
        let depth = 5;
        let packing_depth = 0;
        for i in (0..2usize.pow(depth as u32)).filter(|i| i % 2 == 1) {
            assert_eq!(compute_level(i, depth, packing_depth), 0);
        }
    }

    /// The level of indices below the packing depth is 0.
    #[test]
    fn packing_depth_level() {
        let depth = 10;
        let packing_depth = 3;
        assert_eq!(
            compute_level(0, depth, packing_depth),
            depth + packing_depth
        );
        assert_eq!(compute_level(1, depth, packing_depth), 0);
        assert_eq!(compute_level(2, depth, packing_depth), 0);
        assert_eq!(compute_level(4, depth, packing_depth), 0);
        assert_eq!(compute_level(8, depth, packing_depth), 3);
    }
}
