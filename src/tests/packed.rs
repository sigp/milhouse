use crate::{Error, List, PackedLeaf, Vector};
use ssz_types::{FixedVector, VariableList};
use tree_hash::TreeHash;
use typenum::U16;

#[test]
fn packed_leaf_push_invalidates_cached_hash() {
    let mut leaf = PackedLeaf::single(1u64);
    let mut expected = [0u8; 32];
    expected[..8].copy_from_slice(&1u64.to_le_bytes());
    assert_eq!(leaf.tree_hash().as_slice(), expected);

    for value in 2..=4u64 {
        leaf.push(value).unwrap();
        let start = (value as usize - 1) * 8;
        expected[start..start + 8].copy_from_slice(&value.to_le_bytes());
        assert_eq!(leaf.tree_hash().as_slice(), expected);
    }
}

#[test]
fn packed_leaf_full_push_preserves_cached_hash() {
    let mut leaf = PackedLeaf::repeat(7u64, 4);
    let hash = leaf.tree_hash();
    assert!(matches!(
        leaf.push(9),
        Err(Error::PackedLeafFull { len: 4 })
    ));
    assert_eq!(leaf.values, vec![7u64; 4]);
    assert_eq!(*leaf.hash.read(), hash);
    assert_eq!(leaf.tree_hash(), hash);
}

#[test]
fn u64_packed_list_build_and_iter() {
    for len in 0..=16u64 {
        let vec = (0..len).map(|i| 2 * i).collect::<Vec<u64>>();
        let list = List::<u64, U16>::new(vec.clone()).unwrap();

        let from_iter = list.iter().copied().collect::<Vec<_>>();
        assert_eq!(vec, from_iter);

        for i in 0..len as usize {
            assert_eq!(list.get(i), vec.get(i));
        }
    }
}

#[test]
fn u64_packed_list_tree_hash() {
    for len in 0..=16u64 {
        let vec = (0..len).map(|i| 2 * i).collect::<Vec<u64>>();
        let list = List::<u64, U16>::new(vec.clone()).unwrap();
        let var_list = VariableList::<u64, U16>::new(vec.clone()).unwrap();

        assert_eq!(list.tree_hash_root(), var_list.tree_hash_root());
    }
}

#[test]
fn u64_packed_vector_build_and_iter() {
    let len = 16;

    let vec = (0..len).map(|i| 2 * i).collect::<Vec<u64>>();
    let vector = Vector::<u64, U16>::new(vec.clone()).unwrap();

    let from_iter = vector.iter().copied().collect::<Vec<_>>();
    assert_eq!(vec, from_iter);

    for i in 0..len as usize {
        assert_eq!(vector.get(i), vec.get(i));
    }
}

#[test]
fn u64_packed_vector_tree_hash() {
    let len = 16;
    let vec = (0..len).map(|i| 2 * i).collect::<Vec<u64>>();
    let vector = Vector::<u64, U16>::new(vec.clone()).unwrap();
    let fixed_vector = FixedVector::<u64, U16>::new(vec).unwrap();

    assert_eq!(vector.tree_hash_root(), fixed_vector.tree_hash_root());
}

#[test]
fn out_of_order_mutations() {
    let mut vec = vec![0; 16];
    let mut list = List::<u64, U16>::new(vec.clone()).unwrap();
    let mutations = vec![
        (4, 12),
        (3, 900),
        (0, 1),
        (15, 2),
        (13, 4),
        (7, 17),
        (9, 3),
        (0, 5),
        (6, 100),
        (5, 42),
    ];

    for (i, v) in mutations {
        *list.get_mut(i).unwrap() = v;
        vec[i] = v;
        assert_eq!(list.get(i), Some(&v));

        list.apply_updates().unwrap();

        assert_eq!(list.get(i), Some(&v));
    }

    assert_eq!(list.to_vec(), vec);
}
