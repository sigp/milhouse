use crate::{Diff, Error, List, ListDiff};
use std::fmt::Debug;
use tree_hash::TreeHash;
use typenum::{Unsigned, U16};

fn check_apply<T, D>(orig: &T, expected: &T, diff: D)
where
    T: PartialEq + Debug + Clone,
    D: Diff<Target = T, Error = Error>,
{
    let mut updated = orig.clone();
    diff.apply_diff(&mut updated).unwrap();
    assert_eq!(&updated, expected);
}

fn diff_and_check_apply<T, D>(orig: &T, updated: &T)
where
    T: PartialEq + Debug + Clone,
    D: Diff<Target = T, Error = Error> + Debug,
{
    let diff = D::compute_diff(orig, updated).unwrap();
    check_apply(orig, updated, diff);
}

fn check_confluence<T, D>(orig: &T, a1: &T, a2: &T, b1: &T, b2: &T)
where
    T: PartialEq + Debug + Clone,
    D: Diff<Target = T, Error = Error> + PartialEq + Debug,
{
    // Every path to a2 and b2 should be part of a valid diff that reproduces the original.
    diff_and_check_apply::<_, D>(orig, a1);
    diff_and_check_apply::<_, D>(a1, a2);
    diff_and_check_apply::<_, D>(orig, a2);

    diff_and_check_apply::<_, D>(orig, b1);
    diff_and_check_apply::<_, D>(b1, b2);
    diff_and_check_apply::<_, D>(orig, b2);

    // a2 and b2 should be equal and have equal diffs from orig.
    assert_eq!(a2, b2);
    let a_diff = D::compute_diff(orig, a2).unwrap();
    let b_diff = D::compute_diff(orig, b2).unwrap();
    assert_eq!(a_diff, b_diff);
}

fn with_updated_index<T, N>(list: &List<T, N>, index: usize, value: T) -> List<T, N>
where
    T: TreeHash + Send + Sync + Clone,
    N: Unsigned,
{
    let mut updated = list.clone();
    *updated.get_mut(index).unwrap() = value;

    updated.apply_updates().unwrap();
    updated.tree_hash_root();
    updated
}

fn extended<T, N>(list: &List<T, N>, values: Vec<T>) -> List<T, N>
where
    T: TreeHash + Send + Sync + Clone,
    N: Unsigned,
{
    let mut updated = list.clone();
    for value in values {
        updated.push(value).unwrap();
    }

    updated.apply_updates().unwrap();
    updated.tree_hash_root();
    updated
}

#[test]
fn confluent_diff_list_u64() {
    let orig = List::<u64, U16>::new(vec![0, 1, 4, 6, 9]).unwrap();

    let a1 = with_updated_index(&orig, 1, 2);
    let a2 = with_updated_index(&a1, 4, 8);

    let b1 = with_updated_index(&orig, 4, 8);
    let b2 = with_updated_index(&b1, 1, 2);

    check_confluence::<_, ListDiff<_, _>>(&orig, &a1, &a2, &b1, &b2);
}

#[test]
fn confluent_diff_list_u64_push_empty() {
    let orig = List::<u64, U16>::new(vec![]).unwrap();

    let a1 = extended(&orig, vec![1, 2, 3, 4, 5, 6]);
    let a2 = extended(&a1, vec![7, 8, 9, 10, 11]);

    let b1 = extended(&orig, vec![1, 2, 3]);
    let b2 = extended(&b1, vec![4, 5, 6, 7, 8, 9, 10, 11]);

    check_confluence::<_, ListDiff<_, _>>(&orig, &a1, &a2, &b1, &b2);
}
