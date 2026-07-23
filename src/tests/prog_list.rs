//! Tests for the mutation and rebase API of `ProgressiveList`.

use crate::progressive_tree::ProgressiveTree;
use crate::{Arc, ProgressiveList, Tree};
use tree_hash::TreeHash;

/// Lengths spanning several progressive subtrees and packing boundaries.
const TEST_LENGTHS: &[usize] = &[0, 1, 2, 3, 4, 5, 8, 16, 17, 20, 21, 64, 65, 100, 129];

fn build(n: usize) -> ProgressiveList<u64> {
    ProgressiveList::new((0..n as u64).collect()).unwrap()
}

/// Return the first (left) binary subtree of a progressive tree.
fn first_left<T: crate::Value>(tree: &ProgressiveTree<T>) -> Option<&Arc<Tree<T>>> {
    match tree {
        ProgressiveTree::ProgressiveZero => None,
        ProgressiveTree::ProgressiveNode { left, .. } => Some(left),
    }
}

#[test]
fn push_then_apply_matches_fresh() {
    for &n in TEST_LENGTHS {
        let mut list = ProgressiveList::<u64>::empty();
        for i in 0..n as u64 {
            list.push(i).unwrap();
        }

        // Length reflects pending pushes immediately.
        assert_eq!(list.len(), n);
        assert_eq!(
            list.get(n.saturating_sub(1)).copied(),
            n.checked_sub(1).map(|x| x as u64)
        );

        list.apply_updates().unwrap();

        let expected = build(n);
        assert_eq!(list.to_vec(), expected.to_vec());
        assert_eq!(list.tree_hash_root(), expected.tree_hash_root());
    }
}

#[test]
fn get_mut_matches_fresh() {
    for &n in TEST_LENGTHS {
        if n == 0 {
            continue;
        }
        for &i in &[0usize, n / 2, n - 1] {
            let mut list = build(n);

            *list.get_mut(i).unwrap() = 1000 + i as u64;
            // Mutation visible before applying.
            assert_eq!(list.get(i).copied(), Some(1000 + i as u64));
            assert!(list.has_pending_updates());

            list.apply_updates().unwrap();
            assert!(!list.has_pending_updates());

            let mut expected_vec: Vec<u64> = (0..n as u64).collect();
            expected_vec[i] = 1000 + i as u64;
            let expected = ProgressiveList::<u64>::new(expected_vec).unwrap();

            assert_eq!(list.to_vec(), expected.to_vec());
            assert_eq!(list.tree_hash_root(), expected.tree_hash_root());
        }
    }
}

#[test]
fn iter_from_offset() {
    for &n in TEST_LENGTHS {
        let list = build(n);
        for &k in &[0usize, n / 2, n] {
            if k > n {
                continue;
            }
            let collected: Vec<u64> = list.iter_from(k).unwrap().copied().collect();
            let expected: Vec<u64> = (k as u64..n as u64).collect();
            assert_eq!(collected, expected, "n={n}, k={k}");
        }
    }
}

#[test]
fn iter_from_with_pending_appends() {
    let mut list = build(4);
    list.push(4).unwrap();
    list.push(5).unwrap();

    // Iterate including pending appends, starting partway through.
    let collected: Vec<u64> = list.iter_from(2).unwrap().copied().collect();
    assert_eq!(collected, vec![2, 3, 4, 5]);
}

#[test]
fn pop_front_matches_fresh() {
    for &n in TEST_LENGTHS {
        for &k in &[0usize, 1, n / 2, n] {
            if k > n {
                continue;
            }
            let mut list = build(n);
            list.pop_front(k).unwrap();

            let expected = ProgressiveList::<u64>::new((k as u64..n as u64).collect()).unwrap();
            assert_eq!(list.to_vec(), expected.to_vec(), "n={n}, k={k}");
            assert_eq!(
                list.tree_hash_root(),
                expected.tree_hash_root(),
                "n={n}, k={k}"
            );
        }
    }
}

#[test]
fn rebase_preserves_contents_and_root() {
    for &n in TEST_LENGTHS {
        if n == 0 {
            continue;
        }
        // `orig` differs from `base` only in the last element, so earlier subtrees are equal.
        let base = build(n);

        let mut orig_vec: Vec<u64> = (0..n as u64).collect();
        *orig_vec.last_mut().unwrap() = 9999;
        let mut orig = ProgressiveList::<u64>::new(orig_vec.clone()).unwrap();

        let root_before = orig.tree_hash_root();
        orig.rebase_on(&base).unwrap();

        // Rebase must not change the logical value or the tree hash.
        assert_eq!(orig.to_vec(), orig_vec, "n={n}");
        assert_eq!(orig.tree_hash_root(), root_before, "n={n}");
    }
}

#[test]
fn rebase_shares_equal_subtrees() {
    // Two independently-built equal lists have distinct backing trees until rebased.
    let v: Vec<u64> = (0..20).collect();
    let base = ProgressiveList::<u64>::new(v.clone()).unwrap();
    let mut other = ProgressiveList::<u64>::new(v).unwrap();

    let base_left = first_left(&base.tree).unwrap();
    let other_left_before = first_left(&other.tree).unwrap();
    assert!(
        !Arc::ptr_eq(base_left, other_left_before),
        "independently built lists should not share memory"
    );

    other.rebase_on(&base).unwrap();

    let other_left_after = first_left(&other.tree).unwrap();
    assert!(
        Arc::ptr_eq(base_left, other_left_after),
        "equal left subtree should be shared after rebase"
    );
}

#[test]
fn rebase_unequal_lists_keeps_correct_values() {
    // Rebasing onto a shorter/different base must still yield the original contents.
    let base = ProgressiveList::<u64>::new((0..5).collect()).unwrap();
    let orig_vec: Vec<u64> = (100..130).collect();
    let mut orig = ProgressiveList::<u64>::new(orig_vec.clone()).unwrap();

    let root_before = orig.tree_hash_root();
    orig.rebase_on(&base).unwrap();

    assert_eq!(orig.to_vec(), orig_vec);
    assert_eq!(orig.tree_hash_root(), root_before);
}

#[test]
fn rebase_with_pending_updates_preserves_updates() {
    let base = build(10);
    let mut orig = build(10);

    *orig.get_mut(3).unwrap() = 333;
    assert!(orig.has_pending_updates());

    // Like `List::rebase_on`, rebasing only touches the backing tree: pending updates survive.
    orig.rebase_on(&base).unwrap();
    assert!(orig.has_pending_updates());
    assert_eq!(orig.get(3).copied(), Some(333));

    orig.apply_updates().unwrap();

    let mut expected_vec: Vec<u64> = (0..10).collect();
    expected_vec[3] = 333;
    let expected = ProgressiveList::<u64>::new(expected_vec).unwrap();
    assert_eq!(orig.to_vec(), expected.to_vec());
    assert_eq!(orig.tree_hash_root(), expected.tree_hash_root());
}

#[test]
fn pop_front_with_pending_updates() {
    let mut list = build(4);
    list.push(4).unwrap();
    *list.get_mut(0).unwrap() = 100;
    assert!(list.has_pending_updates());

    // The rebuild merges pending updates without applying them into a throwaway tree.
    list.pop_front(2).unwrap();
    assert_eq!(list.to_vec(), vec![2, 3, 4]);
    assert!(!list.has_pending_updates());

    let expected = ProgressiveList::<u64>::new(vec![2, 3, 4]).unwrap();
    assert_eq!(list.tree_hash_root(), expected.tree_hash_root());
}

/// Regression test for a replace-only `apply_updates` whose highest changed index lives in a deep
/// spine subtree. The largest updated index must be found by scanning the map: `MaxMap`'s
/// `max_index` does not see replaces made via `get_mut`, so trusting it would stop the spine walk
/// short and silently drop the deep updates.
#[test]
fn replace_in_deep_subtree_then_apply_matches_fresh() {
    // 130 elements spans several progressive subtrees for `u64`.
    let mut list = build(130);

    // Replace a low index and a deep one, both via the CoW `get_mut` path (not `push`).
    *list.get_mut(1).unwrap() = 1111;
    *list.get_mut(129).unwrap() = 9999;
    list.apply_updates().unwrap();

    let mut expected_vec: Vec<u64> = (0..130).collect();
    expected_vec[1] = 1111;
    expected_vec[129] = 9999;
    let expected = ProgressiveList::<u64>::new(expected_vec).unwrap();
    assert_eq!(list.to_vec(), expected.to_vec());
    assert_eq!(list.tree_hash_root(), expected.tree_hash_root());
}
