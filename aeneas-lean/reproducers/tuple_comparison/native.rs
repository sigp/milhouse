//! Native oracle for the callback protocol modeled by Tree/Tuple/Comparison.lean.

use std::cell::RefCell;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::rc::Rc;

#[derive(Clone, Copy)]
enum Answer {
    Bool(bool),
    Panic,
}

struct Probe {
    index: u8,
    ne: Answer,
    calls: Rc<RefCell<Vec<u8>>>,
}

impl PartialEq for Probe {
    fn eq(&self, _: &Self) -> bool {
        self.calls.borrow_mut().push(10 + self.index);
        panic!("unexpected element eq call")
    }

    fn ne(&self, _: &Self) -> bool {
        self.calls.borrow_mut().push(self.index);
        match self.ne {
            Answer::Bool(value) => value,
            Answer::Panic => panic!("element ne sentinel"),
        }
    }
}

fn check(first: Answer, second: Answer, expected: Option<bool>, calls: &[u8]) {
    let observed = Rc::new(RefCell::new(Vec::new()));
    let pair = (
        Probe {
            index: 1,
            ne: first,
            calls: observed.clone(),
        },
        Probe {
            index: 2,
            ne: second,
            calls: observed.clone(),
        },
    );
    let actual = catch_unwind(AssertUnwindSafe(|| pair != pair)).ok();
    assert_eq!(actual, expected);
    assert_eq!(&*observed.borrow(), calls);
}

#[test]
fn first_true_skips_both_eq_methods_and_second_ne() {
    check(Answer::Bool(true), Answer::Panic, Some(true), &[1]);
}

#[test]
fn first_false_delegates_to_second_ne() {
    for answer in [false, true] {
        check(
            Answer::Bool(false),
            Answer::Bool(answer),
            Some(answer),
            &[1, 2],
        );
    }
}

#[test]
fn first_failure_prevents_second_comparison() {
    check(Answer::Panic, Answer::Bool(true), None, &[1]);
}

#[test]
fn second_failure_follows_false_first_comparison() {
    check(Answer::Bool(false), Answer::Panic, None, &[1, 2]);
}
