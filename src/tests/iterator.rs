use crate::{List, Vector};
use tree_hash::Hash256;
use typenum::{Unsigned, U64};

#[test]
fn iter_hash256_vec() {
    type N = U64;
    let n = N::to_u64();
    let vec = (0..n).map(Hash256::from_low_u64_be).collect::<Vec<_>>();
    let vector = Vector::<Hash256, N>::new(vec.clone()).unwrap();

    assert_eq!(vector.iter().cloned().collect::<Vec<_>>(), vec);
}

#[test]
fn iter_hash256_list() {
    type N = U64;
    let n = N::to_u64();
    let vec = (0..n).map(Hash256::from_low_u64_be).collect::<Vec<_>>();
    let list = List::<Hash256, N>::new(vec.clone()).unwrap();

    assert_eq!(list.iter().cloned().collect::<Vec<_>>(), vec);
}
