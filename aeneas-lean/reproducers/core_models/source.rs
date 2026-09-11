#![feature(hint_must_use)]

pub fn map_err<T, E, F, O: FnOnce(E) -> F>(value: Result<T, E>, op: O) -> Result<T, F> {
    value.map_err(op)
}
pub fn must_use<T>(value: T) -> T {
    std::hint::must_use(value)
}
pub fn borrow<T>(value: &T) -> &T {
    <T as std::borrow::Borrow<T>>::borrow(value)
}

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
    use super::{borrow, checked_pow, div_ceil, map_err, must_use, saturating_mul, take};
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
    fn error_mapping_skips_success_and_calls_once_on_error() {
        let calls = Cell::new(0);
        let success: Result<Box<u64>, Box<u64>> = Ok(Box::new(7));
        let pointer = success.as_ref().unwrap().as_ref() as *const u64;
        let result = map_err(success, |error| {
            calls.set(calls.get() + 1);
            *error + 1
        });
        let value = result.unwrap();
        assert_eq!(value.as_ref() as *const u64, pointer);
        assert_eq!(calls.get(), 0);

        let error: Result<u64, Box<u64>> = Err(Box::new(11));
        let result = map_err(error, |error| {
            calls.set(calls.get() + 1);
            *error + 1
        });
        assert_eq!(result, Err(12));
        assert_eq!(calls.get(), 1);
    }

    #[test]
    fn error_mapping_propagates_callback_panic() {
        let calls = Cell::new(0);
        let result = catch_unwind(AssertUnwindSafe(|| {
            map_err::<u64, u64, u64, _>(Err(11), |error| {
                assert_eq!(error, 11);
                calls.set(calls.get() + 1);
                panic!("error mapping failed");
            })
        }));
        assert!(result.is_err());
        assert_eq!(calls.get(), 1);
    }

    #[test]
    fn must_use_moves_without_cloning_or_early_drop() {
        let value = Value(7);
        let returned = must_use(value);
        assert_eq!(returned.0, 7);
        EVENTS.with_borrow(|events| assert!(events.is_empty()));
        drop(returned);
        EVENTS.with_borrow(|events| assert_eq!(*events, vec![Event::Drop(7)]));
    }

    #[test]
    fn blanket_borrow_preserves_the_original_reference() {
        let value = Value(11);
        let returned = borrow(&value);
        assert!(std::ptr::eq(returned, &value));
        assert_eq!(returned.0, 11);
        EVENTS.with_borrow(|events| assert!(events.is_empty()));
        drop(value);
        EVENTS.with_borrow(|events| assert_eq!(*events, vec![Event::Drop(11)]));
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
