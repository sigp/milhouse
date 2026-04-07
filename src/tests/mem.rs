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

#[test]
fn measure_mainnet_field_sizes() {
    use alloy_primitives::FixedBytes;

    let n = 1_000_000;
    type C = typenum::U1099511627776;
    type SPHR = typenum::U8192;
    type EPHV = typenum::U65536;
    type EPSV = typenum::U8192;

    let balances = List::<u64, C>::try_from_iter(0..n as u64).unwrap();
    let participation = List::<u8, C>::try_from_iter(vec![0u8; n]).unwrap();
    let validators = List::<FixedBytes<128>, C>::new(vec![FixedBytes::<128>::ZERO; n]).unwrap();
    let state_roots = crate::Vector::<FixedBytes<32>, SPHR>::default();
    let randao = crate::Vector::<FixedBytes<32>, EPHV>::default();
    let slashings = crate::Vector::<u64, EPSV>::default();

    let mut total = 0;
    for (name, bytes) in [
        ("validators (128B×1M)", validators.total_tree_bytes()),
        ("balances (u64×1M)", balances.total_tree_bytes()),
        ("inactivity (u64×1M)", balances.total_tree_bytes()),
        ("prev_part (u8×1M)", participation.total_tree_bytes()),
        ("curr_part (u8×1M)", participation.total_tree_bytes()),
        ("state_roots (H256×8192)", state_roots.total_tree_bytes()),
        ("block_roots (H256×8192)", state_roots.total_tree_bytes()),
        ("randao_mixes (H256×65536)", randao.total_tree_bytes()),
        ("slashings (u64×8192)", slashings.total_tree_bytes()),
    ] {
        total += bytes;
        eprintln!(
            "  {name:<30} {bytes:>12} bytes {:>8.1} MB",
            bytes as f64 / 1048576.0
        );
    }
    eprintln!(
        "  {:<30} {:>12} bytes {:>8.1} MB",
        "TOTAL",
        total,
        total as f64 / 1048576.0
    );
}

#[test]
fn unique_cow_finalization_advance() {
    // Simulate finalization advance:
    // F_old is the original base. S1..S4 are slot transitions from F_old (few mutations).
    // F_new is an epoch boundary state (all entries rewritten) from F_old.
    // After finalization, F_new becomes the base.
    //
    // total_unique_cow_tree_bytes(F_new, [S1..S4]) should NOT count the full tree
    // per state — the dedup HashSet should catch that S1..S4 all share F_old's nodes.

    let f_old = List::<u64, U1048576>::try_from_iter(0..10_000u64).unwrap();

    // F_new: epoch boundary, ALL entries rewritten (completely new tree)
    let mut f_new = f_old.clone();
    for i in 0..10_000 {
        *f_new.get_mut(i).unwrap() = (i as u64).wrapping_add(1_000_000);
    }
    f_new.apply_updates().unwrap();

    // S1..S4: slot transitions from F_old, few mutations each
    let mut states = Vec::new();
    for s in 0..4 {
        let mut si = f_old.clone();
        for j in 0..10 {
            let idx = (s * 137 + j * 31) % 10_000;
            *si.get_mut(idx).unwrap() = u64::MAX;
        }
        si.apply_updates().unwrap();
        states.push(si);
    }

    // Measure using F_old as base (the correct base) — should be small
    let refs_old: Vec<_> = states.iter().map(|s| s.tree_root()).collect();
    let with_old_base = crate::mem::total_unique_cow_tree_bytes(f_old.tree_root(), &refs_old);

    // Measure using F_new as base (what happens after finalization) — should ALSO be
    // reasonable because the HashSet deduplicates F_old's shared nodes across states
    let refs_new: Vec<_> = states.iter().map(|s| s.tree_root()).collect();
    let with_new_base = crate::mem::total_unique_cow_tree_bytes(f_new.tree_root(), &refs_new);

    let full_tree = f_old.total_tree_bytes();

    eprintln!("with_old_base = {with_old_base}");
    eprintln!("with_new_base = {with_new_base}");
    eprintln!("full_tree     = {full_tree}");
    eprintln!("naive per-state cow_bytes vs F_new:");
    for (i, s) in states.iter().enumerate() {
        eprintln!("  S{i}: {}", s.cow_bytes(&f_new));
    }

    // with_old_base: just the dirty paths from S1..S4 (small)
    assert!(
        with_old_base < full_tree / 4,
        "with_old_base ({with_old_base}) should be much less than full tree ({full_tree})"
    );

    // with_new_base: F_old's tree counted ONCE (from S1's walk) + dirty paths.
    // Should be roughly full_tree + small delta, NOT 4 × full_tree.
    assert!(
        with_new_base < full_tree * 2,
        "with_new_base ({with_new_base}) should be < 2× full tree ({full_tree}) thanks to dedup"
    );

    // Naive per-state sum would be ~4 × full_tree (each state counted independently)
    let naive_sum: usize = states.iter().map(|s| s.cow_bytes(&f_new)).sum();
    assert!(
        with_new_base < naive_sum / 2,
        "dedup ({with_new_base}) should be much less than naive sum ({naive_sum})"
    );
}
