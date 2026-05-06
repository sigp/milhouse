//! Benchmarks for total_unique_cow_tree_bytes simulating a realistic state cache.
//!
//! Each "state" has 4 fields matching the dominant BeaconState fields:
//! - validators (FixedBytes<128> × 1M) — 267 MB, rarely dirty
//! - balances (u64 × 1M) — 42 MB, fully dirty at epoch boundary
//! - inactivity_scores (u64 × 1M) — 42 MB, fully dirty at epoch boundary
//! - participation (u8 × 1M) — 5 MB, fully dirty at epoch boundary
//!
//! Scenarios simulate how the state cache looks in practice:
//! (1) Slot transitions: ~10 balance changes, ~128 participation changes
//! (2) Epoch transitions: all balances + inactivity + participation rewritten
//! (3) Effective balance updates: ~500 validator mutations

use alloy_primitives::FixedBytes;
use criterion::{Criterion, criterion_group, criterion_main};
use milhouse::mem::total_unique_cow_tree_bytes;
use milhouse::{Arc, List, Tree};
use std::hint::black_box;

type C = typenum::U1099511627776;
const N: usize = 1_000_000;

/// A minimal multi-field "state" matching the dominant BeaconState fields.
struct MiniState {
    validators: List<FixedBytes<128>, C>,
    balances: List<u64, C>,
    inactivity: List<u64, C>,
    participation: List<u8, C>,
}

impl MiniState {
    fn new() -> Self {
        MiniState {
            validators: List::new(vec![FixedBytes::<128>::ZERO; N]).unwrap(),
            balances: List::try_from_iter(0..N as u64).unwrap(),
            inactivity: List::try_from_iter(vec![0u64; N]).unwrap(),
            participation: List::try_from_iter(vec![0u8; N]).unwrap(),
        }
    }
}

impl Clone for MiniState {
    fn clone(&self) -> Self {
        MiniState {
            validators: self.validators.clone(),
            balances: self.balances.clone(),
            inactivity: self.inactivity.clone(),
            participation: self.participation.clone(),
        }
    }
}

/// Compute total unique bytes across all fields of all states vs the base.
fn measure_all_fields(base: &MiniState, states: &[MiniState]) -> usize {
    let mut total = 0;

    // Validators
    let base_v = base.validators.tree_root();
    let derived_v: Vec<_> = states.iter().map(|s| s.validators.tree_root()).collect();
    total += total_unique_cow_tree_bytes(base_v, &derived_v);

    // Balances
    let base_b = base.balances.tree_root();
    let derived_b: Vec<_> = states.iter().map(|s| s.balances.tree_root()).collect();
    total += total_unique_cow_tree_bytes(base_b, &derived_b);

    // Inactivity
    let base_i = base.inactivity.tree_root();
    let derived_i: Vec<_> = states.iter().map(|s| s.inactivity.tree_root()).collect();
    total += total_unique_cow_tree_bytes(base_i, &derived_i);

    // Participation
    let base_p = base.participation.tree_root();
    let derived_p: Vec<_> = states.iter().map(|s| s.participation.tree_root()).collect();
    total += total_unique_cow_tree_bytes(base_p, &derived_p);

    total
}

/// Slot transition: ~10 balance changes, ~128 participation changes.
fn apply_slot(state: &mut MiniState, slot: usize) {
    for j in 0..10 {
        let idx = (slot * 137 + j * 7919) % N;
        *state.balances.get_mut(idx).unwrap() = u64::MAX;
    }
    for j in 0..128 {
        let idx = (slot * 251 + j * 31) % N;
        *state.participation.get_mut(idx).unwrap() = 0xFF;
    }
    state.balances.apply_updates().unwrap();
    state.participation.apply_updates().unwrap();
}

/// Epoch transition: all balances + inactivity rewritten, participation replaced.
fn apply_epoch(_base: &MiniState, state: &mut MiniState, epoch: usize) {
    for idx in 0..N {
        *state.balances.get_mut(idx).unwrap() = (idx as u64).wrapping_add(epoch as u64);
    }
    for idx in 0..N {
        *state.inactivity.get_mut(idx).unwrap() = epoch as u64;
    }
    // Participation: new list (epoch rotation)
    state.participation = List::try_from_iter(vec![0u8; N]).unwrap();

    state.balances.apply_updates().unwrap();
    state.inactivity.apply_updates().unwrap();
}

/// Effective balance updates: ~500 validator mutations.
fn apply_eff_balance(state: &mut MiniState, epoch: usize) {
    for j in 0..500 {
        let idx = (epoch * 311 + j * 6271) % N;
        let mut val = FixedBytes::<128>::ZERO;
        val.0[0] = epoch as u8;
        *state.validators.get_mut(idx).unwrap() = val;
    }
    state.validators.apply_updates().unwrap();
}

fn bench_realistic_cache(c: &mut Criterion) {
    let mut group = c.benchmark_group("realistic_cache");
    group.sample_size(10);

    // Scenario 1: 128 slot-transition states (chained, like head-following)
    {
        eprintln!("Building 128 chained slot states (4 fields each)...");
        let base = MiniState::new();
        let mut states = Vec::with_capacity(128);
        let mut prev = base.clone();
        for i in 0..128 {
            let mut s = prev.clone();
            apply_slot(&mut s, i);
            states.push(s.clone());
            prev = s;
        }

        group.bench_function("128_slot_chain", |b| {
            b.iter(|| black_box(measure_all_fields(&base, &states)));
        });

        let bytes = measure_all_fields(&base, &states);
        eprintln!("  128 slot chain: {} MB unique", bytes / (1024 * 1024));
    }

    // Scenario 2: 4 epoch boundary + 124 chained slot states
    {
        eprintln!("Building mixed cache (4 epoch + 124 slot chain)...");
        let base = MiniState::new();
        let mut states = Vec::with_capacity(128);

        for i in 0..4 {
            let mut s = base.clone();
            apply_epoch(&base, &mut s, i + 1);
            states.push(s);
        }

        let mut prev = base.clone();
        for i in 0..124 {
            let mut s = prev.clone();
            apply_slot(&mut s, i);
            states.push(s.clone());
            prev = s;
        }

        group.bench_function("mixed_4epoch_124slot", |b| {
            b.iter(|| black_box(measure_all_fields(&base, &states)));
        });

        let bytes = measure_all_fields(&base, &states);
        eprintln!("  mixed cache: {} MB unique", bytes / (1024 * 1024));
    }

    // Scenario 3: 4 epoch + 4 eff_balance + 120 slot chain
    {
        eprintln!("Building cache with eff_balance updates...");
        let base = MiniState::new();
        let mut states = Vec::with_capacity(128);

        for i in 0..4 {
            let mut s = base.clone();
            apply_epoch(&base, &mut s, i + 1);
            states.push(s);
        }

        for i in 0..4 {
            let mut s = base.clone();
            apply_eff_balance(&mut s, i + 1);
            states.push(s);
        }

        let mut prev = base.clone();
        for i in 0..120 {
            let mut s = prev.clone();
            apply_slot(&mut s, i);
            states.push(s.clone());
            prev = s;
        }

        group.bench_function("mixed_4epoch_4eff_120slot", |b| {
            b.iter(|| black_box(measure_all_fields(&base, &states)));
        });

        let bytes = measure_all_fields(&base, &states);
        eprintln!(
            "  mixed+eff_balance cache: {} MB unique",
            bytes / (1024 * 1024)
        );
    }

    // Scenario 4: Just slot transitions (independent, not chained)
    {
        eprintln!("Building 128 independent slot states...");
        let base = MiniState::new();
        let mut states = Vec::with_capacity(128);
        for i in 0..128 {
            let mut s = base.clone();
            apply_slot(&mut s, i);
            states.push(s);
        }

        group.bench_function("128_slot_independent", |b| {
            b.iter(|| black_box(measure_all_fields(&base, &states)));
        });

        let bytes = measure_all_fields(&base, &states);
        eprintln!(
            "  128 slot independent: {} MB unique",
            bytes / (1024 * 1024)
        );
    }

    group.finish();
}

criterion_group!(benches, bench_realistic_cache);
criterion_main!(benches);
