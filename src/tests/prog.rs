use crate::prog_tree::ProgTree;
use tree_hash::Hash256;

#[test]
fn wow() {
    let empty = ProgTree::<Hash256>::empty();

    let one = empty.push(Hash256::repeat_byte(0x11), 0).unwrap();

    let two = one.push(Hash256::repeat_byte(0x22), 1).unwrap();

    println!("{two:#?}");

    let three = two.push(Hash256::repeat_byte(0x33), 2).unwrap();

    println!("{three:#?}");
}

#[test]
fn wow_u64() {
    let mut tree = ProgTree::<u64>::empty();

    for i in 1..=65 {
        tree = tree.push(i, i as usize - 1).unwrap();
    }

    println!("{tree:#?}");
}

#[test]
fn prog_tree_iterator() {
    let mut tree = ProgTree::<u64>::empty();

    // Build a tree with 65 elements
    for i in 1..=65 {
        tree = tree.push(i, i as usize - 1).unwrap();
    }

    // Iterate and collect all elements
    let collected: Vec<_> = tree.iter(65).copied().collect();

    // Verify we got all 65 elements in order
    assert_eq!(collected.len(), 65);
    for (i, &value) in collected.iter().enumerate() {
        assert_eq!(value, (i + 1) as u64, "Element at index {} should be {}", i, i + 1);
    }
}

#[test]
fn prog_tree_iterator_empty() {
    let tree = ProgTree::<u64>::empty();
    let collected: Vec<_> = tree.iter(0).collect();
    assert_eq!(collected.len(), 0);
}

#[test]
fn prog_tree_iterator_small() {
    let mut tree = ProgTree::<u64>::empty();
    
    // Build a small tree with just 4 elements (one packed leaf)
    for i in 1..=4 {
        tree = tree.push(i, i as usize - 1).unwrap();
    }

    let collected: Vec<_> = tree.iter(4).copied().collect();
    assert_eq!(collected, vec![1, 2, 3, 4]);
}

#[test]
fn prog_tree_iterator_exact_size() {
    let mut tree = ProgTree::<u64>::empty();

    for i in 1..=20 {
        tree = tree.push(i, i as usize - 1).unwrap();
    }

    let iter = tree.iter(20);
    assert_eq!(iter.len(), 20);
    
    let collected: Vec<_> = iter.copied().collect();
    assert_eq!(collected.len(), 20);
}

#[test]
fn prog_tree_iterator_hash256() {
    let mut tree = ProgTree::<Hash256>::empty();

    // Build a tree with non-packed values
    for i in 1..=10 {
        let hash = Hash256::repeat_byte(i as u8);
        tree = tree.push(hash, i - 1).unwrap();
    }

    let collected: Vec<_> = tree.iter(10).collect();
    assert_eq!(collected.len(), 10);
    
    // Verify order
    for (i, hash) in collected.iter().enumerate() {
        assert_eq!(**hash, Hash256::repeat_byte((i + 1) as u8));
    }
}
