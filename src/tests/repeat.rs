use crate::{List, Value};
use std::fmt::Debug;
use tree_hash::TreeHash;
use typenum::{Unsigned, U1024, U64, U8};

fn list_test<T: Value + Send + Sync + Debug, N: Unsigned + Debug>(val: T) {
    for n in 96..=N::to_usize() {
        let fast = List::<T, N>::repeat(val.clone(), n).unwrap();
        let slow = List::<T, N>::repeat_slow(val.clone(), n).unwrap();
        assert_eq!(fast, slow);
        assert_eq!(fast.tree_hash_root(), slow.tree_hash_root());
    }
}

#[test]
fn list_u8_8() {
    list_test::<_, U8>(0u8);
    list_test::<_, U8>(143u8);
    list_test::<_, U8>(255u8);
}

#[test]
fn list_u8_64() {
    list_test::<_, U64>(0u8);
    list_test::<_, U64>(143u8);
    list_test::<_, U64>(255u8);
}

#[test]
fn list_u8_1024() {
    list_test::<_, U1024>(0u8);
    list_test::<_, U1024>(143u8);
    list_test::<_, U1024>(255u8);
}

#[test]
fn list_list_u8_64() {
    list_test::<List<u8, U8>, U64>(List::repeat(0u8, 5).unwrap());
    list_test::<List<u8, U8>, U64>(List::repeat(1u8, 1).unwrap());
    list_test::<List<u8, U8>, U64>(List::repeat(255u8, 8).unwrap());
}
