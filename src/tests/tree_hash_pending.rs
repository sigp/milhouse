use crate::{List, Vector};
use tree_hash::TreeHash;
use typenum::{U8, U32, U1024};

#[test]
fn tree_hash_with_pending_updates() {
    let mut list = List::<u64, U32>::new(vec![1, 2, 3, 4]).unwrap();

    // Compute initial hash (no pending updates)
    let hash1 = list.tree_hash_root();

    // Make some updates without applying them
    *list.get_mut(0).unwrap() = 10;
    *list.get_mut(2).unwrap() = 30;

    // Verify we have pending updates
    assert!(list.has_pending_updates());

    // Compute hash WITH pending updates (without calling apply_updates)
    let hash2 = list.tree_hash_root();

    // Hashes should be different
    assert_ne!(hash1, hash2);

    // Apply updates and compute hash again
    list.apply_updates().unwrap();
    let hash3 = list.tree_hash_root();

    // Hash after applying updates should match hash computed with pending updates
    assert_eq!(hash2, hash3);
}

#[test]
fn tree_hash_with_pending_push() {
    let mut list = List::<u64, U32>::new(vec![1, 2, 3]).unwrap();

    // Compute initial hash
    let hash1 = list.tree_hash_root();

    // Push without applying
    list.push(4).unwrap();
    assert!(list.has_pending_updates());

    // Compute hash with pending push
    let hash2 = list.tree_hash_root();
    assert_ne!(hash1, hash2);

    // Apply and verify
    list.apply_updates().unwrap();
    let hash3 = list.tree_hash_root();
    assert_eq!(hash2, hash3);

    // Compare with a list built with the final values
    let list_direct = List::<u64, U32>::new(vec![1, 2, 3, 4]).unwrap();
    assert_eq!(hash3, list_direct.tree_hash_root());
}

#[test]
fn tree_hash_packed_with_pending_updates() {
    // Test with packed types (u8)
    let mut list = List::<u8, U32>::new(vec![1, 2, 3, 4, 5, 6, 7, 8]).unwrap();

    let hash1 = list.tree_hash_root();

    // Update some packed values
    *list.get_mut(0).unwrap() = 10;
    *list.get_mut(7).unwrap() = 80;

    assert!(list.has_pending_updates());

    // Hash with pending updates
    let hash2 = list.tree_hash_root();
    assert_ne!(hash1, hash2);

    // Apply and verify
    list.apply_updates().unwrap();
    let hash3 = list.tree_hash_root();
    assert_eq!(hash2, hash3);
}

#[test]
fn tree_hash_mixed_pending_and_applied() {
    let mut list = List::<u64, U32>::new(vec![1, 2, 3, 4]).unwrap();

    // Apply some updates
    *list.get_mut(0).unwrap() = 10;
    list.apply_updates().unwrap();
    let hash1 = list.tree_hash_root();

    // Add more pending updates
    *list.get_mut(1).unwrap() = 20;
    *list.get_mut(2).unwrap() = 30;
    assert!(list.has_pending_updates());

    // Hash with new pending updates
    let hash2 = list.tree_hash_root();
    assert_ne!(hash1, hash2);

    // Apply and verify
    list.apply_updates().unwrap();
    let hash3 = list.tree_hash_root();
    assert_eq!(hash2, hash3);

    // Compare with directly constructed list
    let list_direct = List::<u64, U32>::new(vec![10, 20, 30, 4]).unwrap();
    assert_eq!(hash3, list_direct.tree_hash_root());
}

#[test]
fn tree_hash_empty_list_with_push() {
    // Test empty list with pending push
    let mut list = List::<u64, U32>::empty();

    let hash1 = list.tree_hash_root();

    // Push to empty list
    list.push(1).unwrap();
    assert!(list.has_pending_updates());

    let hash2 = list.tree_hash_root();
    assert_ne!(hash1, hash2);

    // Apply and verify
    list.apply_updates().unwrap();
    let hash3 = list.tree_hash_root();
    assert_eq!(hash2, hash3);

    // Compare with directly constructed list
    let list_direct = List::<u64, U32>::new(vec![1]).unwrap();
    assert_eq!(hash3, list_direct.tree_hash_root());
}

#[test]
fn tree_hash_large_list_with_pending_updates() {
    // Test with a larger list to exercise deeper tree structures
    let vec: Vec<u64> = (0..100).collect();
    let mut list = List::<u64, U1024>::new(vec.clone()).unwrap();

    let hash1 = list.tree_hash_root();

    // Update multiple elements at different depths in the tree
    *list.get_mut(0).unwrap() = 1000;
    *list.get_mut(16).unwrap() = 1016;
    *list.get_mut(50).unwrap() = 1050;
    *list.get_mut(99).unwrap() = 1099;

    assert!(list.has_pending_updates());

    let hash2 = list.tree_hash_root();
    assert_ne!(hash1, hash2);

    // Apply and verify
    list.apply_updates().unwrap();
    let hash3 = list.tree_hash_root();
    assert_eq!(hash2, hash3);
}

#[test]
fn tree_hash_multiple_pending_pushes() {
    // Test multiple pushes without applying
    let mut list = List::<u64, U32>::new(vec![1, 2]).unwrap();

    let hash1 = list.tree_hash_root();

    // Push multiple elements
    list.push(3).unwrap();
    list.push(4).unwrap();
    list.push(5).unwrap();

    assert!(list.has_pending_updates());

    let hash2 = list.tree_hash_root();
    assert_ne!(hash1, hash2);

    // Apply and verify
    list.apply_updates().unwrap();
    let hash3 = list.tree_hash_root();
    assert_eq!(hash2, hash3);

    // Compare with directly constructed list
    let list_direct = List::<u64, U32>::new(vec![1, 2, 3, 4, 5]).unwrap();
    assert_eq!(hash3, list_direct.tree_hash_root());
}

#[test]
fn tree_hash_vector_with_pending_updates() {
    // Test Vector with pending updates
    let mut vector = Vector::<u64, U8>::new(vec![1, 2, 3, 4, 5, 6, 7, 8]).unwrap();

    let hash1 = vector.tree_hash_root();

    // Update some elements
    *vector.get_mut(0).unwrap() = 10;
    *vector.get_mut(7).unwrap() = 80;

    assert!(vector.has_pending_updates());

    let hash2 = vector.tree_hash_root();
    assert_ne!(hash1, hash2);

    // Apply and verify
    vector.apply_updates().unwrap();
    let hash3 = vector.tree_hash_root();
    assert_eq!(hash2, hash3);
}

#[test]
fn tree_hash_packed_multiple_in_same_leaf() {
    // Test updating multiple values in the same packed leaf
    let mut list = List::<u8, U32>::new(vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).unwrap();

    let hash1 = list.tree_hash_root();

    // Update multiple values that would be in the same packed leaf
    *list.get_mut(0).unwrap() = 10;
    *list.get_mut(1).unwrap() = 20;
    *list.get_mut(2).unwrap() = 30;

    assert!(list.has_pending_updates());

    let hash2 = list.tree_hash_root();
    assert_ne!(hash1, hash2);

    // Apply and verify
    list.apply_updates().unwrap();
    let hash3 = list.tree_hash_root();
    assert_eq!(hash2, hash3);

    // Compare with directly constructed list
    let list_direct = List::<u8, U32>::new(vec![10, 20, 30, 4, 5, 6, 7, 8, 9, 10]).unwrap();
    assert_eq!(hash3, list_direct.tree_hash_root());
}

#[test]
fn tree_hash_single_element_list() {
    // Test with a single element list
    let mut list = List::<u64, U32>::new(vec![1]).unwrap();

    let hash1 = list.tree_hash_root();

    // Update the only element
    *list.get_mut(0).unwrap() = 100;

    assert!(list.has_pending_updates());

    let hash2 = list.tree_hash_root();
    assert_ne!(hash1, hash2);

    // Apply and verify
    list.apply_updates().unwrap();
    let hash3 = list.tree_hash_root();
    assert_eq!(hash2, hash3);

    // Compare with directly constructed list
    let list_direct = List::<u64, U32>::new(vec![100]).unwrap();
    assert_eq!(hash3, list_direct.tree_hash_root());
}

#[test]
fn tree_hash_all_elements_updated() {
    // Test updating all elements in a list
    let mut list = List::<u64, U32>::new(vec![1, 2, 3, 4]).unwrap();

    let hash1 = list.tree_hash_root();

    // Update all elements
    *list.get_mut(0).unwrap() = 10;
    *list.get_mut(1).unwrap() = 20;
    *list.get_mut(2).unwrap() = 30;
    *list.get_mut(3).unwrap() = 40;

    assert!(list.has_pending_updates());

    let hash2 = list.tree_hash_root();
    assert_ne!(hash1, hash2);

    // Apply and verify
    list.apply_updates().unwrap();
    let hash3 = list.tree_hash_root();
    assert_eq!(hash2, hash3);

    // Compare with directly constructed list
    let list_direct = List::<u64, U32>::new(vec![10, 20, 30, 40]).unwrap();
    assert_eq!(hash3, list_direct.tree_hash_root());
}
