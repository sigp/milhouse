use crate::{List, Vector, mem::MemoryTracker};
use typenum::{U1024, U1048576};

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

// ── cow_bytes tests ───────────────────────────────────────────────────

#[test]
fn cow_bytes_identical_is_zero() {
    let list = List::<u64, U1048576>::try_from_iter(0..1000u64).unwrap();
    let clone = list.clone();
    assert_eq!(clone.cow_bytes(&list), 0);
}

#[test]
fn cow_bytes_single_mutation() {
    let base = List::<u64, U1048576>::try_from_iter(0..1000u64).unwrap();
    let mut derived = base.clone();
    *derived.get_mut(0).unwrap() = u64::MAX;
    derived.apply_updates().unwrap();

    let cow = derived.cow_bytes(&base);
    assert!(cow > 0, "single mutation should have non-zero cow_bytes");
    // Should be much less than total (only one root-to-leaf path).
    let total = base.total_tree_bytes();
    assert!(
        cow < total / 10,
        "cow ({cow}) should be << total ({total}) for 1 mutation"
    );
}

#[test]
fn cow_bytes_all_dirty() {
    let base = List::<u64, U1048576>::try_from_iter(0..1000u64).unwrap();
    let mut derived = base.clone();
    for i in 0..1000 {
        *derived.get_mut(i).unwrap() = u64::MAX;
    }
    derived.apply_updates().unwrap();

    let cow = derived.cow_bytes(&base);
    let total = derived.total_tree_bytes();
    // All dirty: cow should be close to total (minus shared Zero subtrees).
    assert!(
        cow > total / 2,
        "all dirty: cow ({cow}) should be > half of total ({total})"
    );
}

#[test]
fn cow_bytes_matches_tracker_differential() {
    // cow_bytes and MemoryTracker differential_size should agree on the tree portion.
    let base = List::<u64, U1048576>::try_from_iter(0..1000u64).unwrap();
    let mut derived = base.clone();
    for i in (0..1000).step_by(10) {
        *derived.get_mut(i).unwrap() = u64::MAX;
    }
    derived.apply_updates().unwrap();

    let cow = derived.cow_bytes(&base);

    let mut tracker = MemoryTracker::default();
    tracker.track_item(&base);
    let tracker_diff = tracker.track_item(&derived).differential_size;

    // tracker_diff includes the List struct overhead; cow_bytes only counts tree nodes.
    // cow_bytes should be close to tracker_diff (within the List struct size).
    let list_overhead = std::mem::size_of::<List<u64, U1048576>>();
    assert!(
        cow <= tracker_diff,
        "cow ({cow}) should be <= tracker_diff ({tracker_diff})"
    );
    assert!(
        tracker_diff - cow <= list_overhead,
        "difference ({}) should be <= list overhead ({list_overhead})",
        tracker_diff - cow
    );
}

#[test]
fn cow_bytes_vector() {
    let base = Vector::<u64, U1024>::new(vec![0u64; 1024]).unwrap();
    let mut derived = base.clone();
    *derived.get_mut(0).unwrap() = 1;
    derived.apply_updates().unwrap();

    let cow = derived.cow_bytes(&base);
    assert!(cow > 0);

    // Clone should be zero.
    let clone = base.clone();
    assert_eq!(clone.cow_bytes(&base), 0);
}

#[test]
fn total_tree_bytes_nonzero() {
    let list = List::<u64, U1048576>::try_from_iter(0..1000u64).unwrap();
    let total = list.total_tree_bytes();
    // 1000 u64 values, packed 4 per leaf = 250 leaves. Each node is ~72 bytes.
    // Total should be in the tens of KB range.
    assert!(
        total > 10_000,
        "total ({total}) should be > 10KB for 1000 u64 entries"
    );
}

#[test]
fn cow_bytes_chain() {
    // A → B → C chain: C.cow_bytes(A) >= C.cow_bytes(B)
    let a = List::<u64, U1048576>::try_from_iter(0..500u64).unwrap();
    let mut b = a.clone();
    for i in 0..250 {
        *b.get_mut(i).unwrap() = u64::MAX;
    }
    b.apply_updates().unwrap();

    let mut c = b.clone();
    for i in 250..500 {
        *c.get_mut(i).unwrap() = u64::MAX;
    }
    c.apply_updates().unwrap();

    let c_vs_a = c.cow_bytes(&a);
    let c_vs_b = c.cow_bytes(&b);
    let b_vs_a = b.cow_bytes(&a);

    assert!(c_vs_a >= c_vs_b, "C vs A ({c_vs_a}) >= C vs B ({c_vs_b})");
    assert!(c_vs_a >= b_vs_a, "C vs A ({c_vs_a}) >= B vs A ({b_vs_a})");
}
