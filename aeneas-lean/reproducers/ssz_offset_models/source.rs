pub fn encode_length(value: usize) -> [u8; 4] {
    ssz::encode_length(value)
}

pub fn read_offset(bytes: &[u8]) -> Result<usize, ssz::DecodeError> {
    ssz::read_offset(bytes)
}

pub fn offset_bytes() -> usize {
    ssz::BYTES_PER_LENGTH_OFFSET
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_inputs_preserve_error_payload() {
        for len in 0..4 {
            assert_eq!(
                read_offset(&[0xff; 4][..len]),
                Err(ssz::DecodeError::InvalidLengthPrefix { len, expected: 4 })
            );
        }
    }

    #[test]
    fn every_bit_and_extreme_values_roundtrip() {
        assert_eq!(offset_bytes(), 4);
        for value in [0, u32::MAX].into_iter().chain((0..32).map(|n| 1 << n)) {
            let bytes = value.to_le_bytes();
            assert_eq!(encode_length(value as usize), bytes);
            assert_eq!(read_offset(&bytes), Ok(value as usize));
        }
    }

    #[test]
    fn mixed_bytes_preserve_order_and_ignore_suffixes() {
        for bytes in [[1, 2, 3, 4], [0xff, 0, 0xa5, 0x5a], [0, 0xff, 1, 0x80]] {
            let value = u32::from_le_bytes(bytes) as usize;
            assert_eq!(encode_length(value), bytes);
            for extra in [0, 1, 4, 17] {
                let mut input = bytes.to_vec();
                input.extend(std::iter::repeat_n(0xff, extra));
                assert_eq!(read_offset(&input), Ok(value));
            }
        }
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn debug_profile_rejects_unrepresentable_offsets() {
        assert!(cfg!(debug_assertions), "audit requires debug assertions");
        for value in [u32::MAX as usize + 1, usize::MAX] {
            assert!(std::panic::catch_unwind(|| encode_length(value)).is_err());
        }
    }
}
