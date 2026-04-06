//! Benchmarks for cow_bytes and total_unique_cow_tree_bytes.
//!
//! Simulates realistic state cache scenarios at mainnet scale:
//! - Slot transitions: few random mutations (balances, roots, participation)
//! - Epoch transitions: all balances + inactivity + participation rewritten
//! - Effective balance updates: ~500 validator records mutated
//!
//! Each scenario is multiplied by expected cache size (128 states) to benchmark
//! total_unique_cow_tree_bytes across the full cache.

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use milhouse::List;
use milhouse::mem::total_unique_cow_tree_bytes;
use std::hint::black_box;

type C = typenum::U1099511627776; // ValidatorRegistryLimit
const N: usize = 1_000_000; // mainnet validator count

/// Build a base list and derive states simulating slot transitions.
/// Each state mutates ~10 random indices (proposer reward + a few attestation rewards).
fn build_slot_states(count: usize) -> (List<u64, C>, Vec<List<u64, C>>) {
    let base = List::<u64, C>::try_from_iter(0..N as u64).unwrap();
    let mut states = Vec::with_capacity(count);
    for i in 0..count {
        let mut s = base.clone();
        // ~10 scattered balance changes per slot
        for j in 0..10 {
            let idx = (i * 137 + j * 7919) % N; // pseudo-random scatter
            *s.get_mut(idx).unwrap() = u64::MAX;
        }
        s.apply_updates().unwrap();
        states.push(s);
    }
    (base, states)
}

/// Build states simulating epoch transitions.
/// Each state has ALL entries rewritten (balances after rewards/penalties).
fn build_epoch_states(count: usize) -> (List<u64, C>, Vec<List<u64, C>>) {
    let base = List::<u64, C>::try_from_iter(0..N as u64).unwrap();
    let mut states = Vec::with_capacity(count);
    for i in 0..count {
        let mut s = base.clone();
        for idx in 0..N {
            *s.get_mut(idx).unwrap() = (idx as u64).wrapping_add(i as u64);
        }
        s.apply_updates().unwrap();
        states.push(s);
    }
    (base, states)
}

/// Build states simulating effective balance updates.
/// ~500 validators have their effective balance changed per epoch.
fn build_eff_balance_states(count: usize) -> (List<u64, C>, Vec<List<u64, C>>) {
    let base = List::<u64, C>::try_from_iter(0..N as u64).unwrap();
    let mut states = Vec::with_capacity(count);
    for i in 0..count {
        let mut s = base.clone();
        for j in 0..500 {
            let idx = (i * 311 + j * 6271) % N;
            *s.get_mut(idx).unwrap() = u64::MAX;
        }
        s.apply_updates().unwrap();
        states.push(s);
    }
    (base, states)
}

/// Build a chain of states: each cloned from the previous, with ~10 mutations.
/// This is the realistic head-following pattern where states share COW nodes.
fn build_chain_states(count: usize) -> (List<u64, C>, Vec<List<u64, C>>) {
    let base = List::<u64, C>::try_from_iter(0..N as u64).unwrap();
    let mut states = Vec::with_capacity(count);
    let mut prev = base.clone();
    for i in 0..count {
        let mut s = prev.clone();
        for j in 0..10 {
            let idx = (i * 137 + j * 7919) % N;
            *s.get_mut(idx).unwrap() = u64::MAX;
        }
        s.apply_updates().unwrap();
        states.push(s.clone());
        prev = s;
    }
    (base, states)
}

/// Mixed cache: 4 epoch boundary states + 124 slot transition states (chained).
fn build_mixed_cache() -> (List<u64, C>, Vec<List<u64, C>>) {
    let base = List::<u64, C>::try_from_iter(0..N as u64).unwrap();
    let mut states = Vec::with_capacity(128);

    // 4 epoch boundary states (all entries rewritten)
    for i in 0..4 {
        let mut s = base.clone();
        for idx in 0..N {
            *s.get_mut(idx).unwrap() = (idx as u64).wrapping_add(i as u64 + 1);
        }
        s.apply_updates().unwrap();
        states.push(s);
    }

    // 124 slot transition states (chained, ~10 mutations each)
    let mut prev = base.clone();
    for i in 0..124 {
        let mut s = prev.clone();
        for j in 0..10 {
            let idx = (i * 137 + j * 7919) % N;
            *s.get_mut(idx).unwrap() = u64::MAX;
        }
        s.apply_updates().unwrap();
        states.push(s.clone());
        prev = s;
    }

    (base, states)
}

fn bench_total_unique(c: &mut Criterion) {
    let mut group = c.benchmark_group("total_unique_cow_tree_bytes");
    group.sample_size(10);

    // Scenario 1: Slot transitions (few mutations per state)
    for cache_size in [32, 64, 128] {
        eprintln!("Building {cache_size} slot states...");
        let (base, states) = build_slot_states(cache_size);
        let refs: Vec<_> = states.iter().map(|s| s.tree_root()).collect();

        group.bench_with_input(
            BenchmarkId::new("slot_transitions", cache_size),
            &(&base, &refs),
            |b, (base, refs)| {
                b.iter(|| black_box(total_unique_cow_tree_bytes(base.tree_root(), refs)));
            },
        );
    }

    // Scenario 2: Epoch transitions (all entries dirty)
    for cache_size in [4, 8, 16] {
        eprintln!("Building {cache_size} epoch states...");
        let (base, states) = build_epoch_states(cache_size);
        let refs: Vec<_> = states.iter().map(|s| s.tree_root()).collect();

        group.bench_with_input(
            BenchmarkId::new("epoch_transitions", cache_size),
            &(&base, &refs),
            |b, (base, refs)| {
                b.iter(|| black_box(total_unique_cow_tree_bytes(base.tree_root(), refs)));
            },
        );
    }

    // Scenario 3: Effective balance updates (~500 mutations per state)
    for cache_size in [32, 64, 128] {
        eprintln!("Building {cache_size} eff_balance states...");
        let (base, states) = build_eff_balance_states(cache_size);
        let refs: Vec<_> = states.iter().map(|s| s.tree_root()).collect();

        group.bench_with_input(
            BenchmarkId::new("eff_balance_updates", cache_size),
            &(&base, &refs),
            |b, (base, refs)| {
                b.iter(|| black_box(total_unique_cow_tree_bytes(base.tree_root(), refs)));
            },
        );
    }

    // Scenario 4: Chain of slot transitions (states cloned from previous)
    for cache_size in [32, 64, 128] {
        eprintln!("Building {cache_size} chain states...");
        let (base, states) = build_chain_states(cache_size);
        let refs: Vec<_> = states.iter().map(|s| s.tree_root()).collect();

        group.bench_with_input(
            BenchmarkId::new("chain_slots", cache_size),
            &(&base, &refs),
            |b, (base, refs)| {
                b.iter(|| black_box(total_unique_cow_tree_bytes(base.tree_root(), refs)));
            },
        );
    }

    // Scenario 5: Mixed realistic cache (4 epoch + 124 chained slots)
    {
        eprintln!("Building mixed cache (4 epoch + 124 chain)...");
        let (base, states) = build_mixed_cache();
        let refs: Vec<_> = states.iter().map(|s| s.tree_root()).collect();

        group.bench_function("mixed_cache_128", |b| {
            b.iter(|| black_box(total_unique_cow_tree_bytes(base.tree_root(), &refs)));
        });
    }

    group.finish();
}

fn bench_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("unique_vs_sum");
    group.sample_size(10);

    // Compare total_unique_cow_tree_bytes vs naive sum of cow_bytes
    // to show how much deduplication helps.
    for (label, cache_size, builder) in [
        ("slot_128", 128usize, build_slot_states as fn(usize) -> _),
        ("eff_balance_128", 128, build_eff_balance_states),
        ("epoch_8", 8, build_epoch_states),
    ] {
        eprintln!("Building comparison: {label}...");
        let (base, states) = builder(cache_size);
        let refs: Vec<_> = states.iter().map(|s| s.tree_root()).collect();

        group.bench_with_input(
            BenchmarkId::new("unique", label),
            &(&base, &refs),
            |b, (base, refs)| {
                b.iter(|| black_box(total_unique_cow_tree_bytes(base.tree_root(), refs)));
            },
        );

        group.bench_with_input(
            BenchmarkId::new("naive_sum", label),
            &(&base, &states),
            |b, (base, states)| {
                b.iter(|| {
                    let sum: usize = states.iter().map(|s| s.cow_bytes(base)).sum();
                    black_box(sum);
                });
            },
        );
    }

    // Print dedup ratio for each scenario
    for (label, cache_size, builder) in [
        ("slot_128", 128usize, build_slot_states as fn(usize) -> _),
        ("chain_128", 128, build_chain_states),
        ("eff_balance_128", 128, build_eff_balance_states),
        ("epoch_8", 8, build_epoch_states),
    ] {
        let (base, states) = builder(cache_size);
        let refs: Vec<_> = states.iter().map(|s| s.tree_root()).collect();
        let unique = total_unique_cow_tree_bytes(base.tree_root(), &refs);
        let naive: usize = states.iter().map(|s| s.cow_bytes(&base)).sum();
        eprintln!(
            "{label}: unique={} naive_sum={} ratio={:.2}x",
            unique,
            naive,
            naive as f64 / unique as f64,
        );
    }

    group.finish();
}

criterion_group!(benches, bench_total_unique, bench_comparison);
criterion_main!(benches);
