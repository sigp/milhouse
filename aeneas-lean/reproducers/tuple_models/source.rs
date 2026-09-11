use std::cmp::Ordering;

pub fn eq<T: PartialEq, U: PartialEq>(left: &(T, U), right: &(T, U)) -> bool {
    <(T, U) as PartialEq>::eq(left, right)
}
pub fn ne<T: PartialEq, U: PartialEq>(left: &(T, U), right: &(T, U)) -> bool {
    <(T, U) as PartialEq>::ne(left, right)
}
pub fn partial_cmp<T: PartialOrd, U: PartialOrd>(
    left: &(T, U),
    right: &(T, U),
) -> Option<Ordering> {
    left.partial_cmp(right)
}
pub fn cmp<T: Ord, U: Ord>(left: &(T, U), right: &(T, U)) -> Ordering {
    left.cmp(right)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    #[derive(Clone, Copy, Debug, PartialEq)]
    enum Method {
        Eq,
        Ne,
        PartialCmp,
        Cmp,
    }

    #[derive(Clone, Copy, Debug, PartialEq)]
    enum Answer {
        Bool(bool),
        Partial(Option<Ordering>),
        Order(Ordering),
        Panic,
    }

    // Deliberately arbitrary answers: the comparison dispatch must not assume
    // that user-provided eq/ne/partial_cmp/cmp methods are interchangeable.
    struct Probe<'a> {
        index: u8,
        method: Method,
        answer: Answer,
        calls: &'a RefCell<Vec<(Method, u8)>>,
    }

    impl Probe<'_> {
        fn invoke(&self, method: Method) -> Answer {
            self.calls.borrow_mut().push((method, self.index));
            assert_eq!(method, self.method, "wrong element method");
            assert_ne!(self.answer, Answer::Panic, "element comparison failed");
            self.answer
        }
    }

    impl PartialEq for Probe<'_> {
        fn eq(&self, _: &Self) -> bool {
            let Answer::Bool(value) = self.invoke(Method::Eq) else {
                panic!("wrong answer type")
            };
            value
        }

        fn ne(&self, _: &Self) -> bool {
            let Answer::Bool(value) = self.invoke(Method::Ne) else {
                panic!("wrong answer type")
            };
            value
        }
    }

    impl Eq for Probe<'_> {}

    impl PartialOrd for Probe<'_> {
        fn partial_cmp(&self, _: &Self) -> Option<Ordering> {
            let Answer::Partial(value) = self.invoke(Method::PartialCmp) else {
                panic!("wrong answer type")
            };
            value
        }
    }

    impl Ord for Probe<'_> {
        fn cmp(&self, _: &Self) -> Ordering {
            let Answer::Order(value) = self.invoke(Method::Cmp) else {
                panic!("wrong answer type")
            };
            value
        }
    }

    fn check(
        method: Method,
        first: Answer,
        second: Answer,
        expected: Answer,
        reaches_second: bool,
    ) {
        let calls = RefCell::new(Vec::new());
        let pair = (
            Probe {
                index: 1,
                method,
                answer: first,
                calls: &calls,
            },
            Probe {
                index: 2,
                method,
                answer: second,
                calls: &calls,
            },
        );
        let actual = catch_unwind(AssertUnwindSafe(|| match method {
            Method::Eq => Answer::Bool(eq(&pair, &pair)),
            Method::Ne => Answer::Bool(ne(&pair, &pair)),
            Method::PartialCmp => Answer::Partial(partial_cmp(&pair, &pair)),
            Method::Cmp => Answer::Order(cmp(&pair, &pair)),
        }))
        .unwrap_or(Answer::Panic);
        assert_eq!(actual, expected, "{method:?}: {first:?}, {second:?}");
        let expected_calls = if reaches_second {
            vec![(method, 1), (method, 2)]
        } else {
            vec![(method, 1)]
        };
        assert_eq!(*calls.borrow(), expected_calls);
    }

    #[test]
    fn equality_callback_protocol() {
        let answers = [Answer::Bool(false), Answer::Bool(true), Answer::Panic];
        for first in answers {
            for second in answers {
                let continues = first == Answer::Bool(true);
                check(
                    Method::Eq,
                    first,
                    second,
                    if continues { second } else { first },
                    continues,
                );
            }
        }
    }

    #[test]
    fn inequality_callback_protocol() {
        let answers = [Answer::Bool(false), Answer::Bool(true), Answer::Panic];
        for first in answers {
            for second in answers {
                let continues = first == Answer::Bool(false);
                check(
                    Method::Ne,
                    first,
                    second,
                    if continues { second } else { first },
                    continues,
                );
            }
        }
    }

    #[test]
    fn partial_order_callback_protocol() {
        let answers = [
            Answer::Partial(None),
            Answer::Partial(Some(Ordering::Less)),
            Answer::Partial(Some(Ordering::Equal)),
            Answer::Partial(Some(Ordering::Greater)),
            Answer::Panic,
        ];
        for first in answers {
            for second in answers {
                let continues = first == Answer::Partial(Some(Ordering::Equal));
                check(
                    Method::PartialCmp,
                    first,
                    second,
                    if continues { second } else { first },
                    continues,
                );
            }
        }
    }

    #[test]
    fn total_order_callback_protocol() {
        let answers = [
            Answer::Order(Ordering::Less),
            Answer::Order(Ordering::Equal),
            Answer::Order(Ordering::Greater),
            Answer::Panic,
        ];
        for first in answers {
            for second in answers {
                let continues = first == Answer::Order(Ordering::Equal);
                check(
                    Method::Cmp,
                    first,
                    second,
                    if continues { second } else { first },
                    continues,
                );
            }
        }
    }
}
