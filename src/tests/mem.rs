use crate::{Vector, mem::MemoryTracker};
use typenum::U1024;

#[test]
fn vector_mutate_last() {
    let v1 = Vector::<u64, U1024>::new(vec![1; 1024]).unwrap();
    let mut v2 = v1.clone();
    *v2.get_mut(1023).unwrap() = 2;
    v2.apply_updates().unwrap();

    let mut tracker = MemoryTracker::default();
    let v1_stats = tracker.track_item(&v1);
    let v2_stats = tracker.track_item(&v2);

    // Total size is equal.
    assert_eq!(v1_stats.total_size, v2_stats.total_size);

    // Differential size for v1 is equal to its total size (nothing to diff against).
    assert_eq!(v1_stats.total_size, v1_stats.differential_size);

    // The differential size of the second list should be less than 2% of the total size.
    assert!(50 * v2_stats.differential_size < v2_stats.total_size);
}
