pub fn pow(value: usize, exponent: u32) -> usize {
    value.pow(exponent)
}

#[cfg(test)]
mod tests {
    use super::pow;
    use std::hint::black_box;
    use std::panic::catch_unwind;

    fn reference(value: usize, exponent: u32) -> Option<usize> {
        let mut product = 1;
        for _ in 0..exponent {
            if value != 0 && product > usize::MAX / value {
                return None;
            }
            product *= value;
        }
        Some(product)
    }

    #[test]
    fn power_matches_repeated_multiplication_and_overflow() {
        for value in [0, 1, 2, 3, 4, usize::MAX / 2, usize::MAX] {
            for exponent in [0, 1, 2, 3, 7, 8, 15, 16, usize::BITS - 1, usize::BITS] {
                let expected = reference(value, exponent);
                let actual = catch_unwind(|| pow(black_box(value), black_box(exponent))).ok();
                assert_eq!(actual, expected, "{value}^{exponent}");
            }
        }
    }

    #[test]
    fn zero_exponents_return_one_for_every_boundary_base() {
        for value in [0, 1, 2, usize::MAX / 2, usize::MAX] {
            assert_eq!(pow(value, 0), 1);
        }
    }

    #[test]
    fn final_bit_does_not_square_the_base_unnecessarily() {
        assert_eq!(pow(usize::MAX, 1), usize::MAX);
        assert_eq!(pow(2, usize::BITS - 1), 1usize << (usize::BITS - 1));
        assert!(catch_unwind(|| pow(2, usize::BITS)).is_err());
        assert!(catch_unwind(|| pow(usize::MAX, 2)).is_err());
    }

    #[test]
    fn maximum_exponents_terminate_with_exact_results() {
        for exponent in [u32::MAX - 1, u32::MAX] {
            assert_eq!(pow(black_box(0), black_box(exponent)), 0);
            assert_eq!(pow(black_box(1), black_box(exponent)), 1);
            assert!(catch_unwind(|| pow(black_box(2), black_box(exponent))).is_err());
            assert!(catch_unwind(|| pow(black_box(usize::MAX), black_box(exponent))).is_err());
        }
    }
}
