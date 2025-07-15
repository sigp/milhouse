use super::{Large, arb_hash256, arb_large, arb_list, arb_vect};
use crate::{List, Vector};
use proptest::prelude::*;
use tree_hash::Hash256;
use typenum::{U1, U2, U3, U4, U7, U8, U9, U32, U33, U1024};

macro_rules! list_test {
    ($name:ident, $T:ty, $N:ty) => {
        // Use default strategy (assumes existence of an `Arbitrary` impl).
        list_test!($name, $T, $N, any::<$T>());
    };
    ($name:ident, $T:ty, $N:ty, $strat:expr) => {
        proptest! {
            #[test]
            fn $name(
                orig_vec in arb_list::<$T, $N, _>(&$strat),
                base_vec in arb_list::<$T, $N, _>(&$strat),
            ) {
                let orig = List::<$T, $N>::new(orig_vec).unwrap();
                let base = List::<$T, $N>::new(base_vec).unwrap();
                let mut rebased = orig.clone();
                rebased.rebase_on(&base).unwrap();
                assert_eq!(rebased, orig);
            }
        }
    };
}

macro_rules! vect_test {
    ($name:ident, $T:ty, $N:ty) => {
        // Use default strategy (assumes existence of an `Arbitrary` impl).
        vect_test!($name, $T, $N, any::<$T>());
    };
    ($name:ident, $T:ty, $N:ty, $strat:expr) => {
        proptest! {
            #[test]
            fn $name(
                orig_vec in arb_vect::<$T, $N, _>(&$strat),
                base_vec in arb_vect::<$T, $N, _>(&$strat)
            ) {
                let orig = Vector::<$T, $N>::new(orig_vec).unwrap();
                let base = Vector::<$T, $N>::new(base_vec).unwrap();
                let mut rebased = orig.clone();
                rebased.rebase_on(&base).unwrap();
                assert_eq!(rebased, orig);
            }
        }
    };
}

mod list {
    use super::*;

    list_test!(u8_1, u8, U1);
    list_test!(u8_2, u8, U2);
    list_test!(u8_3, u8, U3);
    list_test!(u8_4, u8, U4);
    list_test!(u8_7, u8, U7);
    list_test!(u8_8, u8, U8);
    list_test!(u8_9, u8, U9);
    list_test!(u8_32, u8, U32);
    list_test!(u8_33, u8, U33);
    list_test!(u8_1024, u8, U1024);

    list_test!(u64_1, u64, U1);
    list_test!(u64_2, u64, U2);
    list_test!(u64_3, u64, U3);
    list_test!(u64_4, u64, U4);
    list_test!(u64_7, u64, U7);
    list_test!(u64_8, u64, U8);
    list_test!(u64_9, u64, U9);
    list_test!(u64_32, u64, U32);
    list_test!(u64_33, u64, U33);
    list_test!(u64_1024, u64, U1024);

    list_test!(hash256_1, Hash256, U1, arb_hash256());
    list_test!(hash256_2, Hash256, U2, arb_hash256());
    list_test!(hash256_3, Hash256, U3, arb_hash256());
    list_test!(hash256_4, Hash256, U4, arb_hash256());
    list_test!(hash256_7, Hash256, U7, arb_hash256());
    list_test!(hash256_8, Hash256, U8, arb_hash256());
    list_test!(hash256_9, Hash256, U9, arb_hash256());
    list_test!(hash256_32, Hash256, U32, arb_hash256());
    list_test!(hash256_33, Hash256, U33, arb_hash256());
    list_test!(hash256_1024, Hash256, U1024, arb_hash256());

    list_test!(large_1, Large, U1, arb_large());
    list_test!(large_2, Large, U2, arb_large());
    list_test!(large_3, Large, U3, arb_large());
    list_test!(large_4, Large, U4, arb_large());
    list_test!(large_7, Large, U7, arb_large());
    list_test!(large_8, Large, U8, arb_large());
    list_test!(large_9, Large, U9, arb_large());
    list_test!(large_32, Large, U32, arb_large());
    list_test!(large_33, Large, U33, arb_large());
    list_test!(large_1024, Large, U1024, arb_large());
}

mod vect {
    use super::*;

    vect_test!(u8_1, u8, U1);
    vect_test!(u8_2, u8, U2);
    vect_test!(u8_3, u8, U3);
    vect_test!(u8_4, u8, U4);
    vect_test!(u8_7, u8, U7);
    vect_test!(u8_8, u8, U8);
    vect_test!(u8_9, u8, U9);
    vect_test!(u8_32, u8, U32);
    vect_test!(u8_33, u8, U33);
    vect_test!(u8_1024, u8, U1024);

    vect_test!(u64_1, u64, U1);
    vect_test!(u64_2, u64, U2);
    vect_test!(u64_3, u64, U3);
    vect_test!(u64_4, u64, U4);
    vect_test!(u64_7, u64, U7);
    vect_test!(u64_8, u64, U8);
    vect_test!(u64_9, u64, U9);
    vect_test!(u64_32, u64, U32);
    vect_test!(u64_33, u64, U33);
    vect_test!(u64_1024, u64, U1024);

    vect_test!(hash256_1, Hash256, U1, arb_hash256());
    vect_test!(hash256_2, Hash256, U2, arb_hash256());
    vect_test!(hash256_3, Hash256, U3, arb_hash256());
    vect_test!(hash256_4, Hash256, U4, arb_hash256());
    vect_test!(hash256_7, Hash256, U7, arb_hash256());
    vect_test!(hash256_8, Hash256, U8, arb_hash256());
    vect_test!(hash256_9, Hash256, U9, arb_hash256());
    vect_test!(hash256_32, Hash256, U32, arb_hash256());
    vect_test!(hash256_33, Hash256, U33, arb_hash256());
    vect_test!(hash256_1024, Hash256, U1024, arb_hash256());

    vect_test!(large_1, Large, U1, arb_large());
    vect_test!(large_2, Large, U2, arb_large());
    vect_test!(large_3, Large, U3, arb_large());
    vect_test!(large_4, Large, U4, arb_large());
    vect_test!(large_7, Large, U7, arb_large());
    vect_test!(large_8, Large, U8, arb_large());
    vect_test!(large_9, Large, U9, arb_large());
    vect_test!(large_32, Large, U32, arb_large());
    vect_test!(large_33, Large, U33, arb_large());
    vect_test!(large_1024, Large, U1024, arb_large());
}
