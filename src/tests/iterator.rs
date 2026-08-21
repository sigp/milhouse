use crate::{Error, List, Vector};
use tree_hash::Hash256;
use typenum::{U33, U64, Unsigned};

#[test]
fn hash256_vec_iter() {
    type N = U64;
    let n = N::to_u64();
    let vec = (0..n)
        .map(|n| Hash256::right_padding_from(&n.to_le_bytes()))
        .collect::<Vec<_>>();
    let vector = Vector::<Hash256, N>::new(vec.clone()).unwrap();

    assert_eq!(vector.iter().cloned().collect::<Vec<_>>(), vec);
}

#[test]
fn hash256_list_iter() {
    type N = U64;
    let n = N::to_u64();
    let vec = (0..n)
        .map(|n| Hash256::right_padding_from(&n.to_le_bytes()))
        .collect::<Vec<_>>();
    let list = List::<Hash256, N>::new(vec.clone()).unwrap();

    assert_eq!(list.iter().cloned().collect::<Vec<_>>(), vec);
}

#[test]
fn hash256_list_iter_from() {
    type N = U64;
    let n = N::to_usize();
    let vec = (0..n as u64)
        .map(|n| Hash256::right_padding_from(&n.to_le_bytes()))
        .collect::<Vec<_>>();
    let list = List::<Hash256, N>::new(vec.clone()).unwrap();

    for i in 0..=n {
        assert_eq!(
            list.iter_from(i).unwrap().cloned().collect::<Vec<_>>(),
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
        .map(|n| Hash256::right_padding_from(&n.to_le_bytes()))
        .collect::<Vec<_>>();
    let vect = Vector::<Hash256, N>::new(vec.clone()).unwrap();

    for i in 0..=n {
        assert_eq!(
            vect.iter_from(i).unwrap().cloned().collect::<Vec<_>>(),
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

#[test]
fn hash256_list_iter_rev() {
    type N = U64;
    let n = N::to_u64();
    let vec = (0..n)
        .map(|n| Hash256::right_padding_from(&n.to_le_bytes()))
        .collect::<Vec<_>>();
    let list = List::<Hash256, N>::new(vec.clone()).unwrap();

    assert_eq!(
        list.iter().rev().cloned().collect::<Vec<_>>(),
        vec.iter().rev().cloned().collect::<Vec<_>>()
    );
}

#[test]
fn hash256_vector_iter_rev() {
    type N = U64;
    let n = N::to_u64();
    let vec = (0..n)
        .map(|n| Hash256::right_padding_from(&n.to_le_bytes()))
        .collect::<Vec<_>>();
    let vector = Vector::<Hash256, N>::new(vec.clone()).unwrap();

    assert_eq!(
        vector.iter().rev().cloned().collect::<Vec<_>>(),
        vec.iter().rev().cloned().collect::<Vec<_>>()
    );
}

#[test]
fn u64_list_iter_rev_partial() {
    type N = U33;
    let vec: Vec<u64> = (0..33).collect();
    let list = List::<u64, N>::new(vec.clone()).unwrap();

    assert_eq!(
        list.iter().rev().cloned().collect::<Vec<_>>(),
        vec.iter().rev().cloned().collect::<Vec<_>>()
    );
}

#[test]
fn list_iter_from_rev() {
    type N = U64;
    let n = N::to_usize();
    let vec: Vec<u64> = (0..n as u64).collect();
    let list = List::<u64, N>::new(vec.clone()).unwrap();

    for i in 0..=n {
        assert_eq!(
            list.iter_from(i)
                .unwrap()
                .rev()
                .cloned()
                .collect::<Vec<_>>(),
            vec[i..].iter().rev().cloned().collect::<Vec<_>>()
        );
    }
}

#[test]
fn list_iter_mixed_next_back() {
    type N = U64;
    let vec: Vec<u64> = (0..8).collect();
    let list = List::<u64, N>::new(vec.clone()).unwrap();

    let mut iter = list.iter();
    let mut collected = Vec::new();
    while let Some(v) = iter.next() {
        collected.push(*v);
        if let Some(v) = iter.next_back() {
            collected.push(*v);
        }
    }
    while let Some(v) = iter.next_back() {
        collected.push(*v);
    }

    let mut expected = Vec::new();
    let mut front = 0usize;
    let mut back = vec.len();
    while front < back {
        expected.push(vec[front]);
        front += 1;
        if front < back {
            back -= 1;
            expected.push(vec[back]);
        }
    }

    assert_eq!(collected, expected);
}

#[test]
fn list_iter_rev_empty() {
    type N = U64;
    let list = List::<u64, N>::empty();
    assert_eq!(list.iter().rev().count(), 0);
}

#[test]
fn list_iter_rev_single() {
    type N = U64;
    let list = List::<u64, N>::new(vec![42]).unwrap();
    let mut iter = list.iter();
    assert_eq!(iter.next_back().map(|v| *v), Some(42));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
}

#[test]
fn list_iter_rev_with_updates() {
    type N = U64;
    let vec: Vec<u64> = (0..8).collect();
    let mut list = List::<u64, N>::new(vec).unwrap();
    *list.get_mut(1).unwrap() = 100;
    *list.get_mut(6).unwrap() = 200;

    let mut expected: Vec<u64> = (0..8).collect();
    expected[1] = 100;
    expected[6] = 200;

    assert_eq!(
        list.iter().rev().cloned().collect::<Vec<_>>(),
        expected.iter().rev().cloned().collect::<Vec<_>>()
    );
}

#[test]
fn list_iter_rev_pending_push() {
    use typenum::U2;
    let h = Hash256::ZERO;
    let mut list = List::<Hash256, U2>::empty();
    list.push(h).unwrap();
    list.apply_updates().unwrap();
    list.push(h).unwrap();

    let fwd: Vec<_> = list.iter().cloned().collect();
    assert_eq!(list.iter().rev().cloned().collect::<Vec<_>>(), {
        let mut rev = fwd.clone();
        rev.reverse();
        rev
    });
}

#[test]
fn list_iter_from_rev_pending_push() {
    use typenum::U4;
    let h = Hash256::ZERO;
    let mut list = List::<Hash256, U4>::empty();
    list.push(h).unwrap();
    list.apply_updates().unwrap();
    list.push(h).unwrap();
    list.push(h).unwrap();

    let fwd: Vec<_> = list.iter().cloned().collect();
    for start in 0..list.len() {
        assert_eq!(
            list.iter_from(start)
                .unwrap()
                .rev()
                .cloned()
                .collect::<Vec<_>>(),
            fwd[start..].iter().rev().cloned().collect::<Vec<_>>()
        );
    }
}

#[test]
fn list_iter_size_hint_tracks_both_cursors() {
    type N = U64;
    let list = List::<u64, N>::new((0..6).collect()).unwrap();
    let mut iter = list.iter();

    assert_eq!(iter.size_hint(), (6, Some(6)));
    assert_eq!(iter.next().copied(), Some(0));
    assert_eq!(iter.size_hint(), (5, Some(5)));
    assert_eq!(iter.next_back().copied(), Some(5));
    assert_eq!(iter.size_hint(), (4, Some(4)));
    assert_eq!(iter.next_back().copied(), Some(4));
    assert_eq!(iter.size_hint(), (3, Some(3)));
}

#[test]
fn list_iter_from_len_is_empty_both_directions() {
    type N = U64;
    let list = List::<u64, N>::new((0..5).collect()).unwrap();
    let mut iter = list.iter_from(list.len()).unwrap();
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
    assert_eq!(iter.size_hint(), (0, Some(0)));
}

#[test]
fn packed_reverse_from_end_consumes_exactly_once() {
    use typenum::U8;
    let vec: Vec<u64> = (0..8).collect();
    let list = List::<u64, U8>::new(vec.clone()).unwrap();
    let mut iter = list.iter();

    for expected in vec.iter().rev() {
        assert_eq!(iter.next_back(), Some(expected));
    }
    assert_eq!(iter.next_back(), None);
    assert_eq!(iter.next(), None);
}
