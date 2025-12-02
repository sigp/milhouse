use crate::List;
use proptest::prelude::*;
use ssz_derive::{Decode, Encode};
use tree_hash::Hash256;
use tree_hash_derive::TreeHash;
use typenum::{U4, Unsigned};

mod operations;
mod rebase;
mod tree_hash_and_ssz;

pub fn arb_index(n: usize) -> impl Strategy<Value = usize> {
    any::<proptest::sample::Index>().prop_map(move |index| index.index(n))
}

pub fn arb_list<T, N, S>(strategy: S) -> impl Strategy<Value = Vec<T>>
where
    S: Strategy<Value = T>,
    T: std::fmt::Debug,
    N: Unsigned + std::fmt::Debug,
{
    proptest::collection::vec(strategy, 0..=N::to_usize())
}

pub fn arb_vect<T, N, S>(strategy: S) -> impl Strategy<Value = Vec<T>>
where
    S: Strategy<Value = T>,
    T: std::fmt::Debug,
    N: Unsigned + std::fmt::Debug,
{
    proptest::collection::vec(strategy, N::to_usize())
}

pub fn arb_hash256() -> impl Strategy<Value = Hash256> {
    proptest::array::uniform32(any::<u8>()).prop_map(Hash256::from)
}

/// Strategy for generating initial values for a progressive list.
/// Unlike `arb_list`, this has no length limit, but we cap it at a reasonable
/// size for testing purposes.
pub fn arb_progressive_list<T, S>(strategy: S, max_len: usize) -> impl Strategy<Value = Vec<T>>
where
    S: Strategy<Value = T>,
    T: std::fmt::Debug,
{
    proptest::collection::vec(strategy, 0..=max_len)
}

/// Struct with multiple fields shared by multiple proptests.
#[derive(Debug, Clone, PartialEq, Encode, Decode, TreeHash)]
pub struct Large {
    pub a: u64,
    pub b: u8,
    pub c: Hash256,
    pub d: List<u64, U4>,
}

pub fn arb_large() -> impl Strategy<Value = Large> {
    (
        any::<u64>(),
        any::<u8>(),
        arb_hash256(),
        arb_list::<_, U4, _>(any::<u64>()),
    )
        .prop_map(|(a, b, c, d)| Large {
            a,
            b,
            c,
            d: List::new(d).unwrap(),
        })
}
