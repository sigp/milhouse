use super::{arb_hash256, arb_large, arb_list, arb_vect, Large};
use crate::{List, Vector};
use proptest::prelude::*;
use ssz::{Decode, Encode};
use ssz_types::{FixedVector, VariableList};
use tree_hash::{Hash256, TreeHash};
use typenum::{U1, U1024, U2, U3, U32, U33, U4, U7, U8, U9};

macro_rules! list_test {
    ($name:ident, $T:ty, $N:ty) => {
        // Use default strategy (assumes existence of an `Arbitrary` impl).
        list_test!($name, $T, $N, any::<$T>());
    };
    ($name:ident, $T:ty, $N:ty, $strat:expr) => {
        proptest! {
            #[test]
            fn $name(
                init in arb_list::<$T, $N, _>(&$strat)
            ) {
                let list = List::<$T, $N>::new(init.clone()).unwrap();
                let var_list = VariableList::<$T, $N>::new(init).unwrap();

                let ssz_bytes = list.as_ssz_bytes();

                // SSZ roundtrip
                assert_eq!(List::from_ssz_bytes(&ssz_bytes).unwrap(), list);

                // SSZ encoding matches VariableList
                assert_eq!(ssz_bytes, var_list.as_ssz_bytes());

                // Tree hash matches VariableList
                assert_eq!(list.tree_hash_root(), var_list.tree_hash_root());
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
                init in arb_vect::<$T, $N, _>(&$strat)
            ) {
                let vect = Vector::<$T, $N>::new(init.clone()).unwrap();
                let fixed_vect = FixedVector::<$T, $N>::new(init).unwrap();

                let ssz_bytes = vect.as_ssz_bytes();

                // SSZ roundtrip
                assert_eq!(Vector::from_ssz_bytes(&ssz_bytes).unwrap(), vect);

                // SSZ encoding matches FixedVector
                assert_eq!(ssz_bytes, fixed_vect.as_ssz_bytes());

                // Tree hash matches FixedVector
                assert_eq!(vect.tree_hash_root(), fixed_vect.tree_hash_root());
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
