use proptest::prelude::*;
use tree_hash::Hash256;
use typenum::Unsigned;

mod operations;

pub fn arb_index(n: usize) -> impl Strategy<Value = usize> {
    any::<proptest::sample::Index>().prop_map(move |index| index.index(n))
}

pub fn arb_list<T, N, S>(strategy: S) -> impl Strategy<Value = Vec<T>>
where
    S: Strategy<Value = T>,
    N: Unsigned + std::fmt::Debug,
{
    proptest::collection::vec(strategy, 0..=N::to_usize())
}

pub fn arb_vect<T, N, S>(strategy: S) -> impl Strategy<Value = Vec<T>>
where
    S: Strategy<Value = T>,
    N: Unsigned + std::fmt::Debug,
{
    proptest::collection::vec(strategy, N::to_usize())
}

pub fn arb_hash256() -> impl Strategy<Value = Hash256> {
    proptest::array::uniform32(any::<u8>()).prop_map(Hash256::from)
}
