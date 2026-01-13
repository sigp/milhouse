use crate::List;
use tree_hash::TreeHash;
use typenum::U32;

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
