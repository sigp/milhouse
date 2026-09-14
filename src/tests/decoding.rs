use crate::{ProgressiveList, Value};
use itertools::process_results;
use ssz::{Decode, DecodeError, Encode};
use std::fmt::Debug;

// The implementation before the concrete streaming cursor was introduced.
fn original_decode<T: Value>(bytes: &[u8]) -> Result<ProgressiveList<T>, DecodeError> {
    if bytes.is_empty() {
        Ok(ProgressiveList::empty())
    } else if <T as Decode>::is_ssz_fixed_len() {
        let width = <T as Decode>::ssz_fixed_len();
        if width == 0 {
            return Err(DecodeError::ZeroLengthItem);
        }
        process_results(bytes.chunks(width).map(T::from_ssz_bytes), |iter| {
            ProgressiveList::try_from_iter(iter).map_err(|e| {
                DecodeError::BytesInvalid(format!("Error building ssz ProgressiveList: {e:?}"))
            })
        })?
    } else {
        ssz::decode_list_of_variable_length_items(bytes, None)
    }
}

fn assert_decode<T: Value + Debug>(bytes: &[u8]) {
    let actual = ProgressiveList::<T>::from_ssz_bytes(bytes);
    let expected = original_decode::<T>(bytes);
    match (actual, expected) {
        (Ok(actual), Ok(expected)) => {
            assert_eq!(actual.to_vec(), expected.to_vec());
            assert!(!actual.has_pending_updates());
            assert_eq!(actual.len(), expected.len());
        }
        (actual, expected) => assert_eq!(actual, expected, "input: {bytes:?}"),
    }
}

#[test]
fn fixed_decoder_matches_original_including_short_chunks() {
    for n in [0, 1, 4, 5, 20, 21, 84, 85] {
        let bytes = (0..n as u64).collect::<Vec<_>>().as_ssz_bytes();
        assert_decode::<u64>(&bytes);
        for end in bytes.len().saturating_sub(8)..bytes.len() {
            assert_decode::<u64>(&bytes[..end]);
        }
    }
    for byte in 0..=u8::MAX {
        assert_decode::<bool>(&[1, byte, 0]);
    }
}

#[test]
fn variable_decoder_matches_original_for_valid_and_damaged_offsets() {
    for n in [0, 1, 4, 5, 20, 21, 84, 85] {
        let values: Vec<ProgressiveList<u64>> = (0..n)
            .map(|i| ProgressiveList::new(vec![i as u64; i % 4]).unwrap())
            .collect();
        let bytes = values.as_ssz_bytes();
        assert_decode::<ProgressiveList<u64>>(&bytes);
        for end in 0..bytes.len() {
            assert_decode::<ProgressiveList<u64>>(&bytes[..end]);
        }
        for index in 0..n {
            for offset in [0, 1, 3, 4, n * 4 - 1, n * 4, bytes.len(), bytes.len() + 1] {
                let mut damaged = bytes.clone();
                damaged[index * 4..index * 4 + 4].copy_from_slice(&(offset as u32).to_le_bytes());
                assert_decode::<ProgressiveList<u64>>(&damaged);
            }
        }
    }
}

#[test]
fn variable_decoder_preserves_offset_and_payload_error_precedence() {
    // The first payload is invalid bool data. An invalid second offset must
    // win over that decode error; an invalid third offset must lose to it.
    for second in 0u32..=16 {
        for third in 0u32..=16 {
            let mut bytes = 12u32.to_le_bytes().to_vec();
            bytes.extend_from_slice(&second.to_le_bytes());
            bytes.extend_from_slice(&third.to_le_bytes());
            bytes.extend_from_slice(&[2, 1, 0]);
            assert_decode::<ProgressiveList<bool>>(&bytes);
        }
    }
}
