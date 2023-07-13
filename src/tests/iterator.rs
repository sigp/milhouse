use crate::{Error, List, Vector};
use tree_hash::Hash256;
use typenum::{Unsigned, U64};

#[test]
fn hash256_vec_iter() {
    type N = U64;
    let n = N::to_u64();
    let vec = (0..n).map(Hash256::from_low_u64_be).collect::<Vec<_>>();
    let vector = Vector::<Hash256, N>::new(vec.clone()).unwrap();

    assert_eq!(
        vector
            .iter()
            .map(|item| item.into_owned())
            .collect::<Vec<_>>(),
        vec
    );
}

#[test]
fn hash256_list_iter() {
    type N = U64;
    let n = N::to_u64();
    let vec = (0..n).map(Hash256::from_low_u64_be).collect::<Vec<_>>();
    let list = List::<Hash256, N>::new(vec.clone()).unwrap();

    assert_eq!(
        list.iter()
            .map(|item| item.into_owned())
            .collect::<Vec<_>>(),
        vec
    );
}

#[test]
fn hash256_list_iter_from() {
    type N = U64;
    let n = N::to_usize();
    let vec = (0..n as u64)
        .map(Hash256::from_low_u64_be)
        .collect::<Vec<_>>();
    let list = List::<Hash256, N>::new(vec.clone()).unwrap();

    for i in 0..=n {
        assert_eq!(
            list.iter_from(i)
                .unwrap()
                .map(|item| item.into_owned())
                .collect::<Vec<_>>(),
            &vec[i..]
        );
    }

    assert_eq!(
        list.iter_from(n + 1).unwrap_err(),
        Error::OutOfBoundsIterFrom {
            index: n + 1,
            len: n
        }
    );
}

#[test]
fn hash256_vector_iter_from() {
    type N = U64;
    let n = N::to_usize();
    let vec = (0..n as u64)
        .map(Hash256::from_low_u64_be)
        .collect::<Vec<_>>();
    let vect = Vector::<Hash256, N>::new(vec.clone()).unwrap();

    for i in 0..=n {
        assert_eq!(
            vect.iter_from(i)
                .unwrap()
                .map(|item| item.into_owned())
                .collect::<Vec<_>>(),
            &vec[i..]
        );
    }

    assert_eq!(
        vect.iter_from(n + 1).unwrap_err(),
        Error::OutOfBoundsIterFrom {
            index: n + 1,
            len: n
        }
    );
}
