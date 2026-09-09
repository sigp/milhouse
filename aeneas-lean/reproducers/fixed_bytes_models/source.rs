use alloy_primitives::FixedBytes;

pub fn clone<const N: usize>(value: &FixedBytes<N>) -> FixedBytes<N> {
    value.clone()
}
pub fn eq<const N: usize>(left: &FixedBytes<N>, right: &FixedBytes<N>) -> bool {
    left.eq(right)
}
pub fn default<const N: usize>() -> FixedBytes<N> {
    FixedBytes::default()
}
pub fn zero<const N: usize>() -> FixedBytes<N> {
    FixedBytes::ZERO
}
pub fn is_zero<const N: usize>(value: &FixedBytes<N>) -> bool {
    value.is_zero()
}

#[cfg(test)]
mod tests {
    use super::{clone, default, eq, is_zero, zero};
    use alloy_primitives::FixedBytes;

    #[test]
    fn zero_and_default_cover_empty_and_multiple_array_lengths() {
        fn check<const N: usize>() {
            let value = zero::<N>();
            assert_eq!(value.0, [0; N]);
            assert_eq!(default::<N>().0, [0; N]);
            assert!(eq(&value, &default::<N>()));
            assert!(is_zero(&value));
        }
        check::<0>();
        check::<1>();
        check::<31>();
        check::<32>();
        check::<33>();
        check::<64>();
    }

    #[test]
    fn clone_preserves_every_byte_and_leaves_the_original_unchanged() {
        let value = FixedBytes(core::array::from_fn::<_, 32, _>(|i| (i * 7) as u8));
        let mut copied = clone(&value);
        assert_eq!(copied.0, value.0);
        copied.0[17] ^= 0xff;
        assert_eq!(value.0[17], 119);
        assert_ne!(copied.0[17], value.0[17]);
    }

    #[test]
    fn equality_detects_a_difference_at_every_cache_byte() {
        let value = FixedBytes([0xa5; 32]);
        assert!(eq(&value, &clone(&value)));
        for index in 0..32 {
            let mut changed = clone(&value);
            changed.0[index] ^= 1;
            assert!(!eq(&value, &changed));
            assert!(!eq(&changed, &value));
        }
    }

    #[test]
    fn zero_check_detects_every_nonzero_cache_bit() {
        for bit in 0..256 {
            let mut value = zero::<32>();
            value.0[bit / 8] = 1 << (bit % 8);
            assert!(!is_zero(&value));
        }
    }
}
