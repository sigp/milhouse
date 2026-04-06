//! Benchmark cow_bytes: pairwise tree walk for measuring COW cost.
//!
//! Tests at mainnet scale (1M, 2M entries) with varying numbers of dirty leaves.

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use milhouse::List;
use std::hint::black_box;

type C = typenum::U1099511627776; // ValidatorRegistryLimit

fn make_u64_pair(n: usize, dirty: usize) -> (List<u64, C>, List<u64, C>) {
    let base = List::<u64, C>::try_from_iter(0..n as u64).unwrap();
    let mut derived = base.clone();
    let step = if dirty == 0 || dirty >= n {
        1
    } else {
        n / dirty
    };
    let mut count = 0;
    for i in (0..n).step_by(step) {
        if count >= dirty {
            break;
        }
        *derived.get_mut(i).unwrap() = u64::MAX;
        count += 1;
    }
    derived.apply_updates().unwrap();
    (base, derived)
}

fn bench_cow_bytes(c: &mut Criterion) {
    let mut group = c.benchmark_group("cow_bytes");
    group.sample_size(10);

    for (n, dirty, label) in [
        (1_000_000, 0, "1M_0dirty"),
        (1_000_000, 1, "1M_1dirty"),
        (1_000_000, 128, "1M_128dirty"),
        (1_000_000, 10_000, "1M_10kdirty"),
        (1_000_000, 1_000_000, "1M_all_dirty"),
        (2_000_000, 1, "2M_1dirty"),
        (2_000_000, 128, "2M_128dirty"),
        (2_000_000, 2_000_000, "2M_all_dirty"),
    ] {
        eprintln!("Building {label}...");
        let (base, derived) = make_u64_pair(n, dirty);

        group.bench_with_input(
            BenchmarkId::new("list_u64", label),
            &(&base, &derived),
            |b, (base, derived)| {
                b.iter(|| {
                    black_box(derived.cow_bytes(base));
                });
            },
        );
    }

    group.finish();
}

fn bench_cow_bytes_correctness(c: &mut Criterion) {
    // Verify cow_bytes values are reasonable.
    let mut group = c.benchmark_group("correctness_check");
    group.sample_size(10);

    // Identical: should be 0.
    let (base, derived) = make_u64_pair(1000, 0);
    let cow = derived.cow_bytes(&base);
    assert_eq!(cow, 0, "identical lists should have 0 cow_bytes");

    // 1 dirty: should be > 0.
    let (base, derived) = make_u64_pair(1000, 1);
    let cow = derived.cow_bytes(&base);
    assert!(cow > 0, "1 dirty leaf should have non-zero cow_bytes");
    eprintln!("1000 entries, 1 dirty: cow_bytes = {cow}");

    // All dirty: should be large.
    let (base, derived) = make_u64_pair(1000, 1000);
    let cow = derived.cow_bytes(&base);
    eprintln!("1000 entries, all dirty: cow_bytes = {cow}");

    // Clone (no mutation): should be 0.
    let base = List::<u64, C>::try_from_iter(0..1000u64).unwrap();
    let clone = base.clone();
    assert_eq!(clone.cow_bytes(&base), 0, "clone should be 0");

    group.bench_function("noop", |b| b.iter(|| black_box(0)));
    group.finish();
}

criterion_group!(benches, bench_cow_bytes, bench_cow_bytes_correctness);
criterion_main!(benches);
