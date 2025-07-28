use crate::List;
use tree_hash::Hash256;
use typenum::{U16, U32, Unsigned};

#[test]
fn build_partial_hash256_list() {
    type N = U16;
    let n = N::to_usize();
    let vec = (0..n as u64)
        .map(|n| Hash256::right_padding_from(&n.to_le_bytes()))
        .collect::<Vec<_>>();

    for k in 0..n {
        let sub_vec = vec[0..k].to_vec();

        let fast_list = List::<Hash256, N>::try_from_iter(sub_vec.clone()).unwrap();
        let slow_list = List::<Hash256, N>::try_from_iter_slow(sub_vec.clone()).unwrap();

        assert_eq!(fast_list, slow_list);
        assert_eq!(fast_list.iter().cloned().collect::<Vec<_>>(), sub_vec);
    }
}

#[test]
fn build_packed_u64_list() {
    type N = U32;
    let n = N::to_usize();
    let vec = (0..n as u64).collect::<Vec<_>>();

    for k in 0..n {
        let sub_vec = vec[0..k].to_vec();

        let fast_list = List::<u64, N>::try_from_iter(sub_vec.clone()).unwrap();
        let slow_list = List::<u64, N>::try_from_iter(sub_vec.clone()).unwrap();

        assert_eq!(fast_list, slow_list);
        assert_eq!(fast_list.iter().cloned().collect::<Vec<_>>(), sub_vec);
    }
}
