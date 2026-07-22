use crate::update_map::MaxMap;
use crate::{List, UpdateMap};
use std::collections::BTreeMap;
use tree_hash::TreeHash;
use typenum::U8;
use vec_map::VecMap;

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

#[test]
fn bulk_update_replace_only_btreemap() {
    // A bulk update with no appends. The highest updated index is below the list length, so the
    // validation must not scan a backwards range (which panics for `BTreeMap`).
    let mut list: List<u64, U8, BTreeMap<usize, u64>> = List::new(vec![0, 1, 2, 3, 4]).unwrap();
    let updates = BTreeMap::from([(1, 11), (2, 22)]);
    list.bulk_update(updates).unwrap();
    list.apply_updates().unwrap();
    assert_eq!(list.to_vec(), vec![0, 11, 22, 3, 4]);
}

#[test]
fn bulk_update_underreported_max_index() {
    // Entries created via `get_mut_with` do not bump `MaxMap::max_key`, so `max_index` can be
    // smaller than the real highest index. Such a map must either be rejected with the list left
    // unchanged, or applied in full. It must never be half applied.
    let mut updates = MaxMap::<VecMap<u64>>::default();
    *updates.get_mut_with(3, |_| Some(33)).unwrap() = 33;

    let mut list: List<u64, U8, MaxMap<VecMap<u64>>> = List::new(vec![0, 1, 2]).unwrap();

    match list.bulk_update(updates) {
        Ok(()) => {
            list.apply_updates().unwrap();
            assert_eq!(list.len(), 4);
            assert_eq!(list.get(3), Some(&33));
            assert_eq!(list.to_vec(), vec![0, 1, 2, 33]);
        }
        Err(_) => {
            assert_eq!(list.to_vec(), vec![0, 1, 2]);
        }
    }

    // The tree hash must always match the visible contents.
    let canonical = List::<u64, U8>::new(list.to_vec()).unwrap();
    assert_eq!(list.tree_hash_root(), canonical.tree_hash_root());
}
