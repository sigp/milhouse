pub fn is_empty<T>(value: &Vec<T>) -> bool {
    value.is_empty()
}
pub fn eq<T: PartialEq<U>, U>(left: &Vec<T>, right: &Vec<U>) -> bool {
    <Vec<T> as PartialEq<Vec<U>>>::eq(left, right)
}
pub fn ne<T: PartialEq<U>, U>(left: &Vec<T>, right: &Vec<U>) -> bool {
    <Vec<T> as PartialEq<Vec<U>>>::ne(left, right)
}

// Retained direct source probes: these access unsupported container internals.
// They are native-tested below, but excluded from the successful extraction roots.
pub fn pop<T>(value: &mut Vec<T>) -> Option<T> {
    value.pop()
}
pub fn next_back<T>(value: &mut std::vec::IntoIter<T>) -> Option<T> {
    value.next_back()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::{Cell, RefCell};
    use std::panic::{AssertUnwindSafe, catch_unwind};

    struct Probe<'a> {
        index: usize,
        answer: Option<bool>,
        calls: &'a RefCell<Vec<usize>>,
    }

    impl PartialEq for Probe<'_> {
        fn eq(&self, _: &Self) -> bool {
            self.calls.borrow_mut().push(usize::MAX);
            panic!("unexpected element eq")
        }

        fn ne(&self, _: &Self) -> bool {
            self.calls.borrow_mut().push(self.index);
            self.answer.expect("element ne failed")
        }
    }

    #[test]
    fn comparisons_preserve_ne_dispatch_and_short_circuits() {
        let answers = [Some(false), Some(true), None];
        for first in answers {
            for second in answers {
                let calls = RefCell::new(Vec::new());
                let pair = vec![
                    Probe {
                        index: 0,
                        answer: first,
                        calls: &calls,
                    },
                    Probe {
                        index: 1,
                        answer: second,
                        calls: &calls,
                    },
                ];
                let expected_ne = match first {
                    Some(false) => second,
                    other => other,
                };
                let expected_calls = if first == Some(false) {
                    vec![0, 1]
                } else {
                    vec![0]
                };
                assert_eq!(
                    catch_unwind(AssertUnwindSafe(|| eq(&pair, &pair))).ok(),
                    expected_ne.map(|b| !b)
                );
                assert_eq!(*calls.borrow(), expected_calls);
                calls.borrow_mut().clear();
                assert_eq!(
                    catch_unwind(AssertUnwindSafe(|| ne(&pair, &pair))).ok(),
                    expected_ne
                );
                assert_eq!(*calls.borrow(), expected_calls);
            }
        }
    }

    #[test]
    fn unequal_lengths_skip_failing_element_comparisons() {
        let calls = RefCell::new(Vec::new());
        let values: Vec<_> = (0..3)
            .map(|index| Probe {
                index,
                answer: None,
                calls: &calls,
            })
            .collect();
        let short: Vec<_> = (0..2)
            .map(|index| Probe {
                index,
                answer: None,
                calls: &calls,
            })
            .collect();
        let empty = Vec::new();
        for (left, right) in [
            (&values, &short),
            (&short, &values),
            (&values, &empty),
            (&empty, &values),
        ] {
            assert!(!eq(left, right));
            assert!(ne(left, right));
        }
        assert!(eq(&empty, &empty));
        assert!(!ne(&empty, &empty));
        assert!(calls.borrow().is_empty());
    }

    #[test]
    fn emptiness_tracks_length_and_ignores_capacity() {
        let mut values = Vec::with_capacity(32);
        let capacity = values.capacity();
        assert!(is_empty(&values));
        values.push(7);
        assert!(!is_empty(&values));
        assert_eq!(pop(&mut values), Some(7));
        assert!(is_empty(&values));
        assert_eq!(values.capacity(), capacity);
        assert_eq!(pop(&mut values), None);
        let mut zero_sized = vec![(); 5];
        assert!(!is_empty(&zero_sized));
        for _ in 0..5 {
            assert_eq!(pop(&mut zero_sized), Some(()));
        }
        assert!(is_empty(&zero_sized));
        assert_eq!(pop(&mut zero_sized), None);
    }

    struct Owned<'a> {
        value: usize,
        drops: &'a Cell<usize>,
    }

    impl Drop for Owned<'_> {
        fn drop(&mut self) {
            self.drops.set(self.drops.get() + 1);
        }
    }

    #[test]
    fn pop_moves_without_cloning_or_dropping_and_preserves_capacity() {
        let drops = Cell::new(0);
        let mut values = Vec::with_capacity(8);
        let capacity = values.capacity();
        values.extend((0..4).map(|value| Owned {
            value,
            drops: &drops,
        }));
        for expected in (0..4).rev() {
            let last = pop(&mut values).unwrap();
            assert_eq!(last.value, expected);
            assert_eq!(drops.get(), 3 - expected);
            assert_eq!(values.len(), expected);
            assert_eq!(values.capacity(), capacity);
            drop(last);
        }
        assert!(pop(&mut values).is_none());
        assert_eq!(drops.get(), 4);
    }

    #[test]
    fn mixed_iteration_returns_each_owned_value_once() {
        let drops = Cell::new(0);
        let mut iter = (0..4)
            .map(|value| Owned {
                value,
                drops: &drops,
            })
            .collect::<Vec<_>>()
            .into_iter();
        let last = next_back(&mut iter).unwrap();
        let first = iter.next().unwrap();
        let next_last = next_back(&mut iter).unwrap();
        let next_first = iter.next().unwrap();
        assert_eq!(
            [last.value, first.value, next_last.value, next_first.value],
            [3, 0, 2, 1]
        );
        assert_eq!(drops.get(), 0);
        assert!(next_back(&mut iter).is_none());
        assert!(iter.next().is_none());
        assert!(next_back(&mut iter).is_none());
        drop((last, first, next_last, next_first, iter));
        assert_eq!(drops.get(), 4);
    }

    #[test]
    fn mixed_iteration_and_remainder_drop_cover_zero_sized_elements() {
        for length in [0, 1, 2, 7, 32] {
            let mut iter = vec![(); length].into_iter();
            for step in 0..length {
                assert_eq!(iter.len(), length - step);
                assert_eq!(
                    if step % 2 == 0 {
                        next_back(&mut iter)
                    } else {
                        iter.next()
                    },
                    Some(())
                );
            }
            assert_eq!(next_back(&mut iter), None);
            assert_eq!(iter.next(), None);
        }
        let drops = Cell::new(0);
        let mut iter = (0..5)
            .map(|value| Owned {
                value,
                drops: &drops,
            })
            .collect::<Vec<_>>()
            .into_iter();
        let last = next_back(&mut iter).unwrap();
        assert_eq!(last.value, 4);
        assert_eq!(drops.get(), 0);
        drop(iter);
        assert_eq!(drops.get(), 4);
        drop(last);
        assert_eq!(drops.get(), 5);
    }
}
