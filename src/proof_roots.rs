//! Concrete callers that make trait bodies reachable during extraction.
//!
//! This module is compiled only by `scripts/aeneas-extract.sh`. The callers
//! invoke the real public implementations; they do not replace their bodies.

use crate::{ProgressiveList, UpdateMap, Value};

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
