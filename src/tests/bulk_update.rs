use crate::List;
use std::collections::BTreeMap;
use typenum::U8;

#[test]
fn bulk_update_push_empty() {
    let mut list: List<u64, U8, BTreeMap<usize, u64>> = List::empty();
    let updates = BTreeMap::from([(0, 0)]);
    list.bulk_update(updates).unwrap();
    assert_eq!(list.len(), 1);
    assert_eq!(*list.get(0).unwrap(), 0);
}

#[test]
fn bulk_update_push_empty_fail() {
    let mut list: List<u64, U8, BTreeMap<usize, u64>> = List::empty();
    let updates = BTreeMap::from([(1, 0)]);
    list.bulk_update(updates).unwrap_err();
    assert_eq!(list.len(), 0);
}

#[test]
fn bulk_update_push_one() {
    let mut list: List<u64, U8, BTreeMap<usize, u64>> = List::new(vec![0, 1, 2, 3, 4]).unwrap();
    let updates = BTreeMap::from([(5, 5)]);
    list.bulk_update(updates).unwrap();
    assert_eq!(list.len(), 6);
    assert_eq!(*list.get(5).unwrap(), 5);
}

#[test]
fn bulk_update_push_two_btreemap() {
    let mut list: List<u64, U8, BTreeMap<usize, u64>> = List::new(vec![0, 1, 2, 3, 4]).unwrap();
    let updates = BTreeMap::from([(5, 5), (6, 6)]);
    list.bulk_update(updates).unwrap();
    assert_eq!(list.len(), 7);
    assert_eq!(*list.get(5).unwrap(), 5);
    assert_eq!(*list.get(6).unwrap(), 6);
}

#[test]
fn bulk_update_with_gap() {
    let mut list: List<u64, U8, BTreeMap<usize, u64>> = List::new(vec![0, 1, 2, 3, 4]).unwrap();
    let updates = BTreeMap::from([(6, 6)]);
    list.bulk_update(updates).unwrap_err();
    list.apply_updates().unwrap();
    assert_eq!(list.len(), 5);
}
