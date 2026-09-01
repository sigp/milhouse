//! Differential tests of `ProgressiveList` merkleization against a direct transcription of
//! EIP-7916.
//!
//! Everything else in the repo compares milhouse against milhouse, so a systematic error in the
//! progressive hashing geometry (swapped child order, wrong terminator, mis-sized subtree) would
//! otherwise go unnoticed. These tests pin the roots to an independent implementation of the
//! spec's `merkleize_progressive`.

use crate::ProgressiveList;
use ethereum_hashing::hash32_concat;
use ssz::Encode;
use tree_hash::{BYTES_PER_CHUNK, Hash256, TreeHash};

/// SSZ `merkleize(chunks, num_leaves)`: the root of a binary tree over `num_leaves` leaves, with
/// `chunks` padded to `num_leaves` using zero chunks.
fn merkleize(chunks: &[Hash256], num_leaves: usize) -> Hash256 {
    assert!(num_leaves.is_power_of_two());
    assert!(chunks.len() <= num_leaves);

    let mut layer: Vec<Hash256> = chunks.to_vec();
    layer.resize(num_leaves, Hash256::ZERO);
    while layer.len() > 1 {
        layer = layer
            .chunks(2)
            .map(|pair| Hash256::from(hash32_concat(pair[0].as_slice(), pair[1].as_slice())))
            .collect();
    }
    layer[0]
}

/// EIP-7916 `merkleize_progressive(chunks, num_leaves=1)`:
///
/// - If `len(chunks) == 0`: the root is a zero value, `Bytes32()`.
/// - Otherwise: `hash(a, b)` where `a = merkleize(chunks[:num_leaves], num_leaves)` and
///   `b = merkleize_progressive(chunks[num_leaves:], num_leaves * 4)`.
fn merkleize_progressive(chunks: &[Hash256], num_leaves: usize) -> Hash256 {
    if chunks.is_empty() {
        return Hash256::ZERO;
    }
    let split = num_leaves.min(chunks.len());
    let a = merkleize(&chunks[..split], num_leaves);
    let b = merkleize_progressive(&chunks[split..], num_leaves * 4);
    Hash256::from(hash32_concat(a.as_slice(), b.as_slice()))
}

/// SSZ `pack(values)`: serialize basic values and partition into zero-padded 32-byte chunks.
fn pack<T: Encode>(values: &[T]) -> Vec<Hash256> {
    let mut bytes = Vec::new();
    for value in values {
        value.ssz_append(&mut bytes);
    }
    bytes.resize(bytes.len().next_multiple_of(BYTES_PER_CHUNK), 0);
    bytes
        .chunks(BYTES_PER_CHUNK)
        .map(Hash256::from_slice)
        .collect()
}

/// `hash_tree_root` of a progressive list of basic (packed) values, per the spec:
/// `mix_in_length(merkleize_progressive(pack(value)), len(value))`.
pub(crate) fn spec_root_basic<T: Encode>(values: &[T]) -> Hash256 {
    tree_hash::mix_in_length(&merkleize_progressive(&pack(values), 1), values.len())
}

/// `hash_tree_root` of a progressive list of composite values, per the spec:
/// `mix_in_length(merkleize_progressive([hash_tree_root(e) for e in value]), len(value))`.
pub(crate) fn spec_root_composite<T: TreeHash>(values: &[T]) -> Hash256 {
    let chunks: Vec<Hash256> = values.iter().map(|v| v.tree_hash_root()).collect();
    tree_hash::mix_in_length(&merkleize_progressive(&chunks, 1), values.len())
}

/// Lengths crossing chunk, subtree, and spine boundaries for all tested packing factors, in
/// elements. The cumulative subtree boundaries are: u64 (4 per chunk): 4/20/84/340/1364;
/// u8 (32 per chunk): 32/160/672/2720; Hash256 (1 per chunk): 1/5/21/85/341.
const TEST_LENGTHS: &[usize] = &[
    0, 1, 2, 3, 4, 5, 8, 16, 17, 20, 21, 31, 32, 33, 64, 65, 84, 85, 100, 129, 160, 161, 256, 340,
    341, 671, 672, 673, 2720, 2721,
];

#[test]
fn progressive_root_matches_spec_u64() {
    for &n in TEST_LENGTHS {
        // Arbitrary distinct values.
        let values: Vec<u64> = (0..n as u64)
            .map(|i| i.wrapping_mul(0x9e3779b97f4a7c15).wrapping_add(1))
            .collect();
        let list = ProgressiveList::<u64>::new(values.clone()).unwrap();
        assert_eq!(list.tree_hash_root(), spec_root_basic(&values), "n={n}");
    }
}

#[test]
fn progressive_root_matches_spec_u8() {
    for &n in TEST_LENGTHS {
        let values: Vec<u8> = (0..n).map(|i| (i % 251 + 1) as u8).collect();
        let list = ProgressiveList::<u8>::new(values.clone()).unwrap();
        assert_eq!(list.tree_hash_root(), spec_root_basic(&values), "n={n}");
    }
}

#[test]
fn progressive_root_matches_spec_hash256() {
    for &n in TEST_LENGTHS {
        let values: Vec<Hash256> = (0..n as u64)
            .map(|i| Hash256::from(hash32_concat(&i.to_le_bytes(), &[])))
            .collect();
        let list = ProgressiveList::<Hash256>::new(values.clone()).unwrap();
        assert_eq!(list.tree_hash_root(), spec_root_composite(&values), "n={n}");
    }
}

/// Pin the incremental-update path (`with_updated_leaves` spine growth) directly to the spec,
/// rather than only transitively via comparisons against fresh builds: build half the list with
/// the builder, then push the rest and apply.
#[test]
fn progressive_root_matches_spec_u64_via_push() {
    for &n in TEST_LENGTHS {
        let values: Vec<u64> = (0..n as u64)
            .map(|i| i.wrapping_mul(0x9e3779b97f4a7c15).wrapping_add(1))
            .collect();
        let split = n / 2;
        let mut list = ProgressiveList::<u64>::new(values[..split].to_vec()).unwrap();
        for value in &values[split..] {
            list.push(*value).unwrap();
        }
        list.apply_updates().unwrap();
        assert_eq!(list.tree_hash_root(), spec_root_basic(&values), "n={n}");
    }
}

#[test]
fn progressive_root_matches_spec_u8_via_push() {
    for &n in TEST_LENGTHS {
        let values: Vec<u8> = (0..n).map(|i| (i % 251 + 1) as u8).collect();
        let split = n / 2;
        let mut list = ProgressiveList::<u8>::new(values[..split].to_vec()).unwrap();
        for value in &values[split..] {
            list.push(*value).unwrap();
        }
        list.apply_updates().unwrap();
        assert_eq!(list.tree_hash_root(), spec_root_basic(&values), "n={n}");
    }
}

#[test]
fn progressive_root_matches_spec_hash256_via_push() {
    for &n in TEST_LENGTHS {
        let values: Vec<Hash256> = (0..n as u64)
            .map(|i| Hash256::from(hash32_concat(&i.to_le_bytes(), &[])))
            .collect();
        let split = n / 2;
        let mut list = ProgressiveList::<Hash256>::new(values[..split].to_vec()).unwrap();
        for value in &values[split..] {
            list.push(*value).unwrap();
        }
        list.apply_updates().unwrap();
        assert_eq!(list.tree_hash_root(), spec_root_composite(&values), "n={n}");
    }
}
