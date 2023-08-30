use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use milhouse::{List, Value, Vector};
use tree_hash::{Hash256, TreeHash};
use typenum::Unsigned;

type C = typenum::U1099511627776;
type D = typenum::U1000000;
const N: u64 = 800_000;
const M: u64 = 1_000_000;

#[inline]
fn tree_hash_root_list<T: Value + Send + Sync, N: Unsigned>(l1: &List<T, N>) -> Hash256 {
    l1.tree_hash_root()
}

#[inline]
fn tree_hash_root_vector<T: Value + Send + Sync, N: Unsigned>(v1: &Vector<T, N>) -> Hash256 {
    v1.tree_hash_root()
}

pub fn tree_hash_root(c: &mut Criterion) {
    let list_size = N;
    let vector_size = M;

    let list_1 = List::<u64, C>::try_from_iter(0..list_size).unwrap();
    let vector_1 = Vector::<u64, D>::try_from_iter(0..vector_size).unwrap();

    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_list", list_size),
        &(list_1),
        |b, l1| {
            b.iter(|| tree_hash_root_list(l1));
        },
    );

    c.bench_with_input(
        BenchmarkId::new("tree_hash_root_vector", vector_size),
        &(vector_1),
        |b, l1| {
            b.iter(|| tree_hash_root_vector(l1));
        },
    );
}

criterion_group!(benches, tree_hash_root);
criterion_main!(benches);
