//! Concrete callers that make trait bodies reachable during extraction.
//!
//! This module is compiled only by `scripts/aeneas-extract.sh`. The callers
//! invoke the real public implementations; they do not replace their bodies.

use crate::{ProgressiveList, UpdateMap, Value};

pub fn cow_into_mut<'a, T: Clone>(handle: crate::Cow<'a, T>) -> Result<&'a mut T, crate::Error> {
    handle.into_mut()
}

pub fn progressive_list_eq<T: Value, U: UpdateMap<T> + PartialEq>(
    left: &ProgressiveList<T, U>,
    right: &ProgressiveList<T, U>,
) -> bool {
    left == right
}

pub fn progressive_list_ssz_bytes_len<T: Value, U: UpdateMap<T>>(
    list: &ProgressiveList<T, U>,
) -> usize {
    ssz::Encode::ssz_bytes_len(list)
}

pub fn progressive_list_ssz_append<T: Value, U: UpdateMap<T>>(
    list: &ProgressiveList<T, U>,
    buf: &mut Vec<u8>,
) {
    ssz::Encode::ssz_append(list, buf);
}

pub fn progressive_list_ssz_fixed_len<T: Value, U: UpdateMap<T>>() -> (bool, usize) {
    (
        <ProgressiveList<T, U> as ssz::Encode>::is_ssz_fixed_len(),
        <ProgressiveList<T, U> as ssz::Encode>::ssz_fixed_len(),
    )
}

pub fn progressive_list_as_ssz_bytes<T: Value, U: UpdateMap<T>>(
    list: &ProgressiveList<T, U>,
) -> Vec<u8> {
    ssz::Encode::as_ssz_bytes(list)
}

pub fn progressive_list_from_ssz_bytes<T: Value, U: UpdateMap<T>>(
    bytes: &[u8],
) -> Result<ProgressiveList<T, U>, ssz::DecodeError> {
    ssz::Decode::from_ssz_bytes(bytes)
}

pub fn progressive_list_decode_metadata<T: Value, U: UpdateMap<T>>() -> (bool, usize) {
    (
        <ProgressiveList<T, U> as ssz::Decode>::is_ssz_fixed_len(),
        <ProgressiveList<T, U> as ssz::Decode>::ssz_fixed_len(),
    )
}

#[cfg(feature = "arbitrary")]
pub fn progressive_list_arbitrary<'a, T, U>(
    input: &mut arbitrary::Unstructured<'a>,
) -> arbitrary::Result<ProgressiveList<T, U>>
where
    T: arbitrary::Arbitrary<'a> + Value,
    U: UpdateMap<T>,
{
    arbitrary::Arbitrary::arbitrary(input)
}

#[cfg(feature = "arbitrary")]
pub fn progressive_list_arbitrary_take_rest<'a, T, U>(
    input: arbitrary::Unstructured<'a>,
) -> arbitrary::Result<ProgressiveList<T, U>>
where
    T: arbitrary::Arbitrary<'a> + Value,
    U: UpdateMap<T>,
{
    arbitrary::Arbitrary::arbitrary_take_rest(input)
}

#[cfg(feature = "arbitrary")]
pub fn progressive_list_arbitrary_size_hint<'a, T, U>(depth: usize) -> (usize, Option<usize>)
where
    T: arbitrary::Arbitrary<'a> + Value,
    U: UpdateMap<T>,
{
    <ProgressiveList<T, U> as arbitrary::Arbitrary>::size_hint(depth)
}

#[cfg(feature = "arbitrary")]
pub fn progressive_list_arbitrary_try_size_hint<'a, T, U>(
    depth: usize,
) -> Result<(usize, Option<usize>), arbitrary::MaxRecursionReached>
where
    T: arbitrary::Arbitrary<'a> + Value,
    U: UpdateMap<T>,
{
    <ProgressiveList<T, U> as arbitrary::Arbitrary>::try_size_hint(depth)
}

pub fn progressive_list_tree_hash_type<T: Value + Send + Sync, U: UpdateMap<T>>()
-> tree_hash::TreeHashType {
    <ProgressiveList<T, U> as tree_hash::TreeHash>::tree_hash_type()
}

pub fn progressive_list_tree_hash_packed_encoding<T: Value + Send + Sync, U: UpdateMap<T>>(
    list: &ProgressiveList<T, U>,
) -> tree_hash::PackedEncoding {
    tree_hash::TreeHash::tree_hash_packed_encoding(list)
}

pub fn progressive_list_tree_hash_packing_factor<T: Value + Send + Sync, U: UpdateMap<T>>() -> usize
{
    <ProgressiveList<T, U> as tree_hash::TreeHash>::tree_hash_packing_factor()
}
