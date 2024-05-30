use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use milhouse::{List, Value};
use typenum::Unsigned;

type C = typenum::U1099511627776;
const N: u64 = 800_000;

#[inline]
fn rebase<T: Value, N: Unsigned>(l1: &List<T, N>, l2: &List<T, N>) -> List<T, N> {
    let mut l1_rebased = l1.clone();
    l1_rebased.rebase_on(l2).unwrap();
    l1_rebased
}

pub fn rebase_list(c: &mut Criterion) {
    let size = N;

    let base_list = List::<u64, C>::try_from_iter(0..size).unwrap();
    let identical = List::<u64, C>::try_from_iter(0..size).unwrap();
    let push_1_back = List::<u64, C>::try_from_iter(0..=size).unwrap();
    let mutate_0 = List::<u64, C>::try_from_iter(std::iter::once(2048).chain(1..size)).unwrap();
    let completely_different = List::<u64, C>::try_from_iter((0..size).rev()).unwrap();

    c.bench_with_input(
        BenchmarkId::new("rebase_identical", size),
        &(identical.clone(), base_list.clone()),
        |b, (l1, l2)| {
            b.iter(|| rebase(l1, l2));
        },
    );
    c.bench_with_input(
        BenchmarkId::new("rebase_push_1_back", size),
        &(push_1_back.clone(), base_list.clone()),
        |b, (l1, l2)| {
            b.iter(|| rebase(l1, l2));
        },
    );
    c.bench_with_input(
        BenchmarkId::new("rebase_mutate0", size),
        &(mutate_0.clone(), base_list.clone()),
        |b, (l1, l2)| {
            b.iter(|| rebase(l1, l2));
        },
    );
    c.bench_with_input(
        BenchmarkId::new("rebase_completely_different", size),
        &(completely_different.clone(), base_list.clone()),
        |b, (l1, l2)| {
            b.iter(|| rebase(l1, l2));
        },
    );
}

criterion_group!(benches, rebase_list);
criterion_main!(benches);
