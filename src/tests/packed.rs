use crate::{List, Vector};
use ssz_types::{FixedVector, VariableList};
use tree_hash::TreeHash;
use typenum::U16;

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
    let fixed_vector = FixedVector::<u64, U16>::new(vec.clone()).unwrap();

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
    }

    assert_eq!(list.to_vec(), vec);
}
