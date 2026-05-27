use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use milhouse::{List, Vector};
use ssz_types::VariableList;
use tree_hash::TreeHash;

type C = typenum::U1099511627776;
type D = typenum::U1000000;
const N: u64 = 1_000_000;

pub fn tree_hash_root(c: &mut Criterion) {
    let size = N;

    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_list", size),
        &size,
        |b, &size| {
            b.iter_batched(
                || List::<u64, C>::try_from_iter(0..size).unwrap(),
                |l1| l1.tree_hash_root(),
                BatchSize::LargeInput,
            );
        },
    );

    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_vector", size),
        &size,
        |b, &size| {
            b.iter_batched(
                || Vector::<u64, D>::try_from_iter(0..size).unwrap(),
                |v1| v1.tree_hash_root(),
                BatchSize::LargeInput,
            );
        },
    );

    // Test `VariableList` as a point of comparison.
    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_variable_list", size),
        &size,
        |b, &size| {
            b.iter_batched(
                || VariableList::<u64, C>::new((0..size).collect()).unwrap(),
                |l1| l1.tree_hash_root(),
                BatchSize::LargeInput,
            );
        },
    );

    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_shared_sequential", size),
        &size,
        |b, &size| {
            b.iter_batched(
                || {
                    let l1 = List::<u64, C>::try_from_iter(0..size).unwrap();
                    let mut l2 = l1.clone();
                    l2.push(99).unwrap();
                    l2.apply_updates().unwrap();
                    (l1, l2)
                },
                |(l1, l2)| {
                    l1.tree_hash_root();
                    l2.tree_hash_root();
                },
                BatchSize::LargeInput,
            );
        },
    );

    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_shared_parallel", size),
        &size,
        |b, &size| {
            b.iter_batched(
                || {
                    let l1 = List::<u64, C>::try_from_iter(0..size).unwrap();
                    let mut l2 = l1.clone();
                    l2.push(99).unwrap();
                    l2.apply_updates().unwrap();
                    (l1, l2)
                },
                |(l1, l2)| {
                    let handle_1 = std::thread::spawn(move || {
                        l1.tree_hash_root();
                    });
                    let handle_2 = std::thread::spawn(move || {
                        l2.tree_hash_root();
                    });

                    handle_1.join().unwrap();
                    handle_2.join().unwrap();
                },
                BatchSize::LargeInput,
            );
        },
    );

    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_independent_sequential", size),
        &size,
        |b, &size| {
            b.iter_batched(
                || {
                    let l1 = List::<u64, C>::try_from_iter(0..size).unwrap();
                    let l2 = List::<u64, C>::try_from_iter((0..size).rev()).unwrap();
                    (l1, l2)
                },
                |(l1, l2)| {
                    l1.tree_hash_root();
                    l2.tree_hash_root();
                },
                BatchSize::LargeInput,
            );
        },
    );

    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_independent_parallel", size),
        &size,
        |b, &size| {
            b.iter_batched(
                || {
                    let l1 = List::<u64, C>::try_from_iter(0..size).unwrap();
                    let l2 = List::<u64, C>::try_from_iter((0..size).rev()).unwrap();
                    (l1, l2)
                },
                |(l1, l2)| {
                    let handle_1 = std::thread::spawn(move || {
                        l1.tree_hash_root();
                    });
                    let handle_2 = std::thread::spawn(move || {
                        l2.tree_hash_root();
                    });

                    handle_1.join().unwrap();
                    handle_2.join().unwrap();
                },
                BatchSize::LargeInput,
            );
        },
    );

    // Build a list with many duplicates, then intra_rebase to create sharing.
    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_intra_rebased", size),
        &size,
        |b, &size| {
            b.iter_batched(
                || {
                    let mut l =
                        List::<u64, C>::try_from_iter((0..size as u64).map(|i| i % 256)).unwrap();
                    l.apply_updates().unwrap();
                    l.tree_hash_root();
                    l.intra_rebase().unwrap();
                    // Mutate one element to invalidate hashes along one path.
                    *l.get_mut(0).unwrap() = 9999;
                    l.apply_updates().unwrap();
                    l
                },
                |l| l.tree_hash_root(),
                BatchSize::LargeInput,
            );
        },
    );
}

criterion_group!(benches, tree_hash_root);
criterion_main!(benches);
