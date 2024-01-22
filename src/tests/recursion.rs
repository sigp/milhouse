use crate::{List, PendingUpdates};
use ssz_derive::{Decode, Encode};
use tree_hash::TreeHash;
use tree_hash_derive::TreeHash;
use typenum::U16;

#[test]
fn recursive_list_list() {
    let mut l = List::<List<u64, U16>, U16>::default();

    l.push(<_>::default()).unwrap();
    l.get_mut(0).unwrap().push(1).unwrap();
    l.apply_updates().unwrap();
    // assert it does not throw
    let h_1 = l.tree_hash_root();

    assert!(!l.has_pending_updates());
    assert_eq!(*l.get(0).unwrap().get(0).unwrap(), 1);

    // Replace value
    *l.get_mut(0).unwrap().get_mut(0).unwrap() = 2;
    assert_eq!(*l.get(0).unwrap().get(0).unwrap(), 2);

    // Commit only top list
    l.apply_updates().unwrap();
    // Root should be different
    assert_ne!(h_1, l.tree_hash_root());
}

/// Struct with multiple fields shared by multiple proptests.
#[derive(Default, Debug, Clone, PartialEq, Encode, Decode, TreeHash)]
pub struct ListContainer {
    a: u8,
    b: List<u64, U16>,
}

impl PendingUpdates for ListContainer {
    fn apply(&mut self) -> Result<(), crate::Error> {
        // TODO use macro derive
        self.b.apply()?;
        Ok(())
    }
}

#[test]
fn recursive_list_container_list() {
    let mut l = List::<ListContainer, U16>::default();

    l.push(<_>::default()).unwrap();
    l.get_mut(0).unwrap().b.push(1).unwrap();
    l.apply_updates().unwrap();
    // assert it does not throw
    let h_1 = l.tree_hash_root();

    assert!(!l.has_pending_updates());
    assert_eq!(*l.get(0).unwrap().b.get(0).unwrap(), 1);

    // Replace value
    *l.get_mut(0).unwrap().b.get_mut(0).unwrap() = 2;
    assert_eq!(*l.get(0).unwrap().b.get(0).unwrap(), 2);

    // Commit only top list
    l.apply_updates().unwrap();
    // Root should be different
    assert_ne!(h_1, l.tree_hash_root());
}
