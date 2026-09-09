pub fn take<T: Default>(place: &mut T) -> T {
    std::mem::take(place)
}
pub fn div_ceil(value: usize, divisor: usize) -> usize {
    value.div_ceil(divisor)
}
pub fn saturating_mul(value: u128, other: u128) -> u128 {
    value.saturating_mul(other)
}
pub fn checked_pow(value: u128, exponent: u32) -> Option<u128> {
    value.checked_pow(exponent)
}

#[cfg(test)]
mod tests {
    use super::{checked_pow, div_ceil, saturating_mul, take};
    use std::cell::{Cell, RefCell};
    use std::panic::{AssertUnwindSafe, catch_unwind};

    #[derive(Debug, PartialEq, Eq)]
    enum Event {
        Default,
        Drop(u64),
    }

    thread_local! {
        static EVENTS: RefCell<Vec<Event>> = const { RefCell::new(Vec::new()) };
        static PANIC_DEFAULT: Cell<bool> = const { Cell::new(false) };
    }

    struct Value(u64);

    impl Default for Value {
        fn default() -> Self {
            EVENTS.with_borrow_mut(|events| events.push(Event::Default));
            assert!(!PANIC_DEFAULT.get(), "default failed");
            Value(0)
        }
    }

    impl Drop for Value {
        fn drop(&mut self) {
            EVENTS.with_borrow_mut(|events| events.push(Event::Drop(self.0)));
        }
    }

    #[test]
    fn take_defaults_once_without_dropping_the_old_value() {
        let mut place = Value(7);
        let old = take(&mut place);
        assert_eq!(old.0, 7);
        assert_eq!(place.0, 0);
        EVENTS.with_borrow(|events| assert_eq!(*events, vec![Event::Default]));
        drop(old);
        EVENTS.with_borrow(|events| assert_eq!(*events, vec![Event::Default, Event::Drop(7)]));
    }

    #[test]
    fn take_keeps_the_old_value_when_default_panics() {
        let mut place = Value(7);
        PANIC_DEFAULT.set(true);
        assert!(catch_unwind(AssertUnwindSafe(|| take(&mut place))).is_err());
        assert_eq!(place.0, 7);
        EVENTS.with_borrow(|events| assert_eq!(*events, vec![Event::Default]));
    }

    #[test]
    fn ceiling_division_rounds_without_intermediate_word_overflow() {
        for value in [0, 1, 2, usize::MAX / 2, usize::MAX - 1, usize::MAX] {
            for divisor in [1, 2, 3, usize::MAX] {
                let expected = (value as u128 + divisor as u128 - 1) / divisor as u128;
                assert_eq!(div_ceil(value, divisor) as u128, expected);
            }
        }
    }

    #[test]
    fn ceiling_division_rejects_zero_divisors() {
        for value in [0, 1, usize::MAX] {
            assert!(catch_unwind(|| div_ceil(value, 0)).is_err());
        }
    }

    #[test]
    fn saturating_multiplication_at_exact_and_overflow_boundaries() {
        for value in [0, 1, 2, 3, u128::MAX / 2, u128::MAX - 1, u128::MAX] {
            for other in [0, 1, 2, 3, u128::MAX] {
                let expected = if other != 0 && value > u128::MAX / other {
                    u128::MAX
                } else {
                    value * other
                };
                assert_eq!(saturating_mul(value, other), expected);
            }
        }
    }

    #[test]
    fn checked_power_matches_repeated_multiplication() {
        fn reference(value: u128, exponent: u32) -> Option<u128> {
            let mut product = 1;
            for _ in 0..exponent {
                if value != 0 && product > u128::MAX / value {
                    return None;
                }
                product *= value;
            }
            Some(product)
        }

        for value in [0, 1, 2, 3, 4, 1 << 64, u128::MAX] {
            for exponent in [0, 1, 2, 3, 63, 64, 80, 81, 127, 128, 129] {
                assert_eq!(checked_pow(value, exponent), reference(value, exponent));
            }
        }
    }

    #[test]
    fn checked_power_handles_large_exponents() {
        for exponent in [u32::MAX - 1, u32::MAX] {
            assert_eq!(checked_pow(0, exponent), Some(0));
            assert_eq!(checked_pow(1, exponent), Some(1));
            assert_eq!(checked_pow(2, exponent), None);
            assert_eq!(checked_pow(u128::MAX, exponent), None);
        }
    }
}
