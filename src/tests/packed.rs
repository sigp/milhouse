use crate::List;
use ssz_types::VariableList;
use tree_hash::TreeHash;
use typenum::U16;

#[test]
fn u64_packed_list_build_and_iter() {
    for len in 0..=16u64 {
        let vec = (0..len).map(|i| 2 * i).collect::<Vec<u64>>();
        let list = List::<u64, U16>::new(vec.clone()).unwrap();

        let from_iter = list.iter().copied().collect::<Vec<_>>();
        assert_eq!(vec, from_iter);
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
