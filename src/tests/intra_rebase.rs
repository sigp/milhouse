use crate::{Arc, List, Tree, Value, Vector};
use ssz::{Decode, Encode};
use std::fmt::Debug;
use tree_hash::{Hash256, TreeHash};
use typenum::{U3, U4, U9, U16, Unsigned};

fn check_list<T, N>(values: Vec<T>)
where
    T: Value + Debug + Send + Sync,
    N: Unsigned + Debug,
{
    let expected = List::<T, N>::new(values.clone()).unwrap();
    let root = expected.tree_hash_root();
    let bytes = expected.as_ssz_bytes();
    let mut pending = List::<T, N>::empty();
    for value in &values {
        pending.push(value.clone()).unwrap();
    }

    for mut list in [expected.clone(), pending] {
        list.intra_rebase().unwrap();

        assert_eq!(list, expected);
        assert_eq!(list.len(), values.len());
        assert_eq!(list.interface.backing.tree.compute_len(), values.len());
        assert_eq!(list.to_vec(), values);
        assert_eq!(list.tree_hash_root(), root);
        assert_eq!(list.as_ssz_bytes(), bytes);
        assert_eq!(list, List::from_ssz_bytes(&bytes).unwrap());

        // Front removal also uses the represented length of the final subtree.
        list.pop_front(1).unwrap();
        assert_eq!(list.to_vec(), values[1..]);
        assert_eq!(list.len(), values.len() - 1);
    }
}

fn check_vector<T, N>(values: Vec<T>)
where
    T: Value + Debug + Send + Sync,
    N: Unsigned + Debug,
{
    let expected = Vector::<T, N>::new(values.clone()).unwrap();
    let root = expected.tree_hash_root();
    let bytes = expected.as_ssz_bytes();
    let mut vector = expected.clone();
    vector.intra_rebase().unwrap();

    assert_eq!(vector, expected);
    assert_eq!(vector.interface.backing.tree.compute_len(), values.len());
    assert_eq!(vector.to_vec(), values);
    assert_eq!(vector.tree_hash_root(), root);
    assert_eq!(vector.as_ssz_bytes(), bytes);
    assert_eq!(vector, Vector::from_ssz_bytes(&bytes).unwrap());
}

#[test]
fn packed_list_preserves_zero_padded_tail() {
    // Eight materialized u64 zeros and a shorter zero-padded subtree have the
    // same hash, including when the final packed leaf is only partially full.
    for len in 9..16 {
        check_list::<u64, U16>(vec![0; len]);
    }
}

#[test]
fn unpacked_list_preserves_zero_padded_tail() {
    check_list::<Hash256, U4>(vec![Hash256::ZERO; 3]);
}

#[test]
fn packed_vector_preserves_zero_padded_tail() {
    check_vector::<u64, U9>(vec![0; 9]);
}

#[test]
fn unpacked_vector_preserves_zero_padded_tail() {
    check_vector::<Hash256, U3>(vec![Hash256::ZERO; 3]);
}

fn root_children_are_shared<T: Value>(tree: &Tree<T>) -> bool {
    match tree {
        Tree::Node { left, right, .. } => Arc::ptr_eq(left, right),
        _ => panic!("expected an internal node"),
    }
}

#[test]
fn full_subtrees_are_still_shared() {
    let values = vec![7u64; 16];
    let mut list = List::<u64, U16>::new(values.clone()).unwrap();
    let mut vector = Vector::<u64, U16>::new(values.clone()).unwrap();
    assert!(!root_children_are_shared(&list.interface.backing.tree));
    assert!(!root_children_are_shared(&vector.interface.backing.tree));

    list.intra_rebase().unwrap();
    vector.intra_rebase().unwrap();

    assert!(root_children_are_shared(&list.interface.backing.tree));
    assert!(root_children_are_shared(&vector.interface.backing.tree));
    assert_eq!(list.to_vec(), values);
    assert_eq!(vector.to_vec(), values);
}
