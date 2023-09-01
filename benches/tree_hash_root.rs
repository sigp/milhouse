use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
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
            b.iter(|| {
                let l1 = List::<u64, C>::try_from_iter(0..size).unwrap();
                l1.tree_hash_root()
            });
        },
    );

    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_vector", size),
        &size,
        |b, &size| {
            b.iter(|| {
                let v1 = Vector::<u64, D>::try_from_iter(0..size).unwrap();
                v1.tree_hash_root()
            });
        },
    );

    // Test `VariableList` as a point of comparison.
    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_variable_list", size),
        &size,
        |b, &size| {
            b.iter(|| {
                let l1 = VariableList::<u64, C>::new((0..size).collect()).unwrap();
                l1.tree_hash_root()
            })
        },
    );
}

criterion_group!(benches, tree_hash_root);
criterion_main!(benches);
