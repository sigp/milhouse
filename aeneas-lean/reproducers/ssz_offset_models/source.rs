pub fn encode_length(value: usize) -> [u8; 4] {
    ssz::encode_length(value)
}

pub fn read_offset(bytes: &[u8]) -> Result<usize, ssz::DecodeError> {
    ssz::read_offset(bytes)
}

pub fn offset_bytes() -> usize {
    ssz::BYTES_PER_LENGTH_OFFSET
}

pub fn container(buf: &mut Vec<u8>, fixed: usize) -> ssz::SszEncoder<'_> {
    ssz::SszEncoder::container(buf, fixed)
}

pub fn finalize<'a>(encoder: &'a mut ssz::SszEncoder<'_>) -> &'a mut Vec<u8> {
    encoder.finalize()
}

pub fn append<T: ssz::Encode>(encoder: &mut ssz::SszEncoder<'_>, item: &T) {
    encoder.append(item)
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

    #[test]
    fn container_preserves_prefix_and_releases_replacement() {
        for fixed in [0, 1, 4, 16] {
            let mut buf = vec![0x99, 0x42];
            drop(container(&mut buf, fixed));
            assert_eq!(buf, [0x99, 0x42]);
            assert!(buf.capacity() >= 2 + fixed);
            let mut encoder = container(&mut buf, fixed);
            encoder.append_parameterized(true, |bytes| {
                assert_eq!(bytes, &[0x99, 0x42]);
                bytes.clear();
                bytes.extend_from_slice(&[0xa5, 0x5a, 7]);
            });
            drop(encoder);
            assert_eq!(buf, [0xa5, 0x5a, 7]);
        }
    }

    #[test]
    fn finalization_moves_payload_and_clears_it() {
        let mut buf = vec![0x99];
        let mut encoder = container(&mut buf, 8);
        encoder.append_parameterized(false, |bytes| {
            assert!(bytes.is_empty());
            bytes.extend_from_slice(&[1, 2]);
        });
        encoder.append_parameterized(false, |bytes| {
            assert_eq!(bytes, &[1, 2]);
            bytes.push(3);
        });
        assert_eq!(
            finalize(&mut encoder),
            &[0x99, 8, 0, 0, 0, 10, 0, 0, 0, 1, 2, 3]
        );
        let output = finalize(&mut encoder);
        output.clear();
        output.push(0xef);
        assert_eq!(finalize(&mut encoder), &[0xef]);
        drop(encoder);
        assert_eq!(buf, [0xef]);
    }

    #[test]
    fn append_panic_preserves_reached_write_order() {
        for fixed in [false, true] {
            let mut buf = vec![0x99];
            let mut encoder = container(&mut buf, 4);
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    encoder.append_parameterized(fixed, |bytes| {
                        if fixed {
                            assert_eq!(bytes, &[0x99]);
                        } else {
                            assert!(bytes.is_empty());
                        }
                        bytes.push(0xff);
                        panic!("append panic sentinel");
                    });
                }))
                .is_err()
            );
            let expected: &[u8] = if fixed {
                &[0x99, 0xff]
            } else {
                &[0x99, 4, 0, 0, 0, 0xff]
            };
            assert_eq!(finalize(&mut encoder), expected);
        }
    }

    #[test]
    fn reserve_overflow_precedes_encoder_creation() {
        let mut buf = vec![0x99];
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _ = container(&mut buf, usize::MAX);
            }))
            .is_err()
        );
        assert_eq!(buf, [0x99]);
    }
}
