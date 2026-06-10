//! Tests for the mutation and rebase API of `ProgressiveList`.

use crate::progressive_tree::ProgressiveTree;
use crate::{Arc, ProgressiveList, Tree};
use tree_hash::{Hash256, TreeHash};

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
fn replace_and_append_in_one_batch() {
    // Mix replaces (existing indices) and appends (new indices) in a single `apply_updates`.
    let mut list = build(10);

    *list.get_mut(0).unwrap() = 100;
    *list.get_mut(9).unwrap() = 109;
    list.push(10).unwrap();
    list.push(11).unwrap();

    assert_eq!(list.len(), 12);
    list.apply_updates().unwrap();

    let mut expected_vec: Vec<u64> = (0..10).collect();
    expected_vec[0] = 100;
    expected_vec[9] = 109;
    expected_vec.push(10);
    expected_vec.push(11);
    let expected = ProgressiveList::<u64>::new(expected_vec).unwrap();

    assert_eq!(list.to_vec(), expected.to_vec());
    assert_eq!(list.tree_hash_root(), expected.tree_hash_root());
}

#[test]
fn get_cow_and_iter_cow() {
    let mut list = build(5);

    {
        let c = list.get_cow(2).unwrap();
        assert_eq!(*c, 2);
        *c.into_mut().unwrap() = 22;
    }
    assert_eq!(list.get(2).copied(), Some(22));

    {
        let mut iter = list.iter_cow();
        while let Some((index, v)) = iter.next_cow() {
            *v.into_mut().unwrap() = (index * 10) as u64;
        }
    }
    list.apply_updates().unwrap();
    assert_eq!(list.to_vec(), vec![0, 10, 20, 30, 40]);
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
fn rebase_with_pending_updates_applies_first() {
    let base = build(10);
    let mut orig = build(10);

    *orig.get_mut(3).unwrap() = 333;
    assert!(orig.has_pending_updates());

    orig.rebase_on(&base).unwrap();
    assert!(!orig.has_pending_updates());

    let mut expected_vec: Vec<u64> = (0..10).collect();
    expected_vec[3] = 333;
    let expected = ProgressiveList::<u64>::new(expected_vec).unwrap();
    assert_eq!(orig.to_vec(), expected.to_vec());
    assert_eq!(orig.tree_hash_root(), expected.tree_hash_root());
}

#[test]
fn mutation_matches_fresh_hash256() {
    // Exercise an unpacked element type (no `PackedLeaf`).
    let n = 40usize;
    let mk = |i: usize| Hash256::repeat_byte(i as u8);

    let mut list = ProgressiveList::<Hash256>::new((0..n).map(mk).collect()).unwrap();
    *list.get_mut(37).unwrap() = Hash256::repeat_byte(0xff);
    list.apply_updates().unwrap();

    let mut expected_vec: Vec<Hash256> = (0..n).map(mk).collect();
    expected_vec[37] = Hash256::repeat_byte(0xff);
    let expected = ProgressiveList::<Hash256>::new(expected_vec).unwrap();

    assert_eq!(list.to_vec(), expected.to_vec());
    assert_eq!(list.tree_hash_root(), expected.tree_hash_root());
}

#[test]
fn bulk_update_then_apply() {
    use crate::update_map::MaxMap;
    use vec_map::VecMap;

    let mut list = build(8);

    let mut updates: MaxMap<VecMap<u64>> = MaxMap::default();
    crate::UpdateMap::insert(&mut updates, 2, 222);
    crate::UpdateMap::insert(&mut updates, 8, 888); // append

    list.bulk_update(updates).unwrap();
    assert_eq!(list.len(), 9);
    list.apply_updates().unwrap();

    let mut expected_vec: Vec<u64> = (0..8).collect();
    expected_vec[2] = 222;
    expected_vec.push(888);
    let expected = ProgressiveList::<u64>::new(expected_vec).unwrap();
    assert_eq!(list.to_vec(), expected.to_vec());
    assert_eq!(list.tree_hash_root(), expected.tree_hash_root());
}
