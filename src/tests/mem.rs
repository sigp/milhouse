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

#[test]
fn cow_bytes_includes_leaf_data() {
    use alloy_primitives::FixedBytes;

    // 10KB per entry, capacity 2. Uses Leaf<T> (unpacked, since size > 32 bytes).
    // cow_bytes must account for the leaf data, not just tree node overhead.
    type Big = FixedBytes<10000>;

    let base = List::<Big, typenum::U2>::new(vec![Box::new(Big::ZERO).as_ref().clone()]).unwrap();
    let mut derived = base.clone();
    *derived.get_mut(0).unwrap() = Box::new(FixedBytes([0xAA; 10000])).as_ref().clone();
    derived.apply_updates().unwrap();

    let cow = derived.cow_bytes(&base);
    assert!(
        cow >= 10000,
        "cow_bytes ({cow}) must be >= 10000 — leaf data must be counted"
    );

    let total = base.total_tree_bytes();
    assert!(
        total >= 10000,
        "total_tree_bytes ({total}) must be >= 10000"
    );
}

// ── total_unique_cow_tree_bytes tests ─────────────────────────────────

#[test]
fn unique_cow_dedup_shared_states() {
    // Two states cloned from the same base, both mutating the same index.
    // Their COW'd paths overlap — unique count should be less than sum of individual.
    let base = List::<u64, U1048576>::try_from_iter(0..1000u64).unwrap();
    let mut s1 = base.clone();
    *s1.get_mut(0).unwrap() = 111;
    s1.apply_updates().unwrap();

    let mut s2 = base.clone();
    *s2.get_mut(0).unwrap() = 222;
    s2.apply_updates().unwrap();

    let base_tree = base.tree_root();
    let individual_sum = s1.cow_bytes(&base) + s2.cow_bytes(&base);
    let unique =
        crate::mem::total_unique_cow_tree_bytes(base_tree, &[s1.tree_root(), s2.tree_root()]);

    // Both mutated the same index but different values → different leaf nodes
    // but shared internal path nodes. Unique should be less than sum.
    assert!(unique > 0);
    assert!(
        unique <= individual_sum,
        "unique ({unique}) should be <= sum of individual ({individual_sum})"
    );
}

#[test]
fn unique_cow_chain() {
    // Chain: base → A → B. B shares A's COW'd nodes.
    let base = List::<u64, U1048576>::try_from_iter(0..1000u64).unwrap();
    let mut a = base.clone();
    for i in 0..500 {
        *a.get_mut(i).unwrap() = u64::MAX;
    }
    a.apply_updates().unwrap();

    let mut b = a.clone();
    for i in 500..1000 {
        *b.get_mut(i).unwrap() = u64::MAX;
    }
    b.apply_updates().unwrap();

    let base_tree = base.tree_root();
    let unique =
        crate::mem::total_unique_cow_tree_bytes(base_tree, &[a.tree_root(), b.tree_root()]);
    let b_alone = b.cow_bytes(&base);

    // B was cloned from A then modified further. B shares A's nodes for indices 0..500
    // but has new nodes for 500..1000. A has its own path nodes for 0..500.
    // Unique should be close to B's cost — A adds only the few path nodes that B replaced.
    let individual_sum = a.cow_bytes(&base) + b.cow_bytes(&base);
    assert!(
        unique < individual_sum,
        "unique ({unique}) should be < sum ({individual_sum}) due to sharing"
    );
    assert!(
        unique >= b_alone,
        "unique ({unique}) should be >= B alone ({b_alone})"
    );
}

#[test]
fn unique_cow_disjoint() {
    // Two states mutating completely different indices — no shared COW nodes.
    let base = List::<u64, U1048576>::try_from_iter(0..10000u64).unwrap();
    let mut s1 = base.clone();
    *s1.get_mut(0).unwrap() = 111;
    s1.apply_updates().unwrap();

    let mut s2 = base.clone();
    *s2.get_mut(9999).unwrap() = 222;
    s2.apply_updates().unwrap();

    let base_tree = base.tree_root();
    let individual_sum = s1.cow_bytes(&base) + s2.cow_bytes(&base);
    let unique =
        crate::mem::total_unique_cow_tree_bytes(base_tree, &[s1.tree_root(), s2.tree_root()]);

    // Disjoint mutations: no shared COW nodes (except possibly root).
    // Unique should be close to (but possibly slightly less than) the sum
    // because the root node might be counted once instead of twice.
    assert!(unique > 0);
    assert!(unique <= individual_sum);
}

#[test]
fn unique_cow_empty() {
    let base = List::<u64, U1048576>::try_from_iter(0..1000u64).unwrap();
    let base_tree = base.tree_root();
    let unique = crate::mem::total_unique_cow_tree_bytes(base_tree, &[]);
    assert_eq!(unique, 0);
}

#[test]
fn unique_cow_clone_only() {
    // Clone without mutation — should be 0.
    let base = List::<u64, U1048576>::try_from_iter(0..1000u64).unwrap();
    let clone = base.clone();
    let base_tree = base.tree_root();
    let unique = crate::mem::total_unique_cow_tree_bytes(base_tree, &[clone.tree_root()]);
    assert_eq!(unique, 0);
}
