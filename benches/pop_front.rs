use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use milhouse::{List, Value};
use typenum::Unsigned;

type C = typenum::U1099511627776;
const N: u64 = 800_000;

#[inline]
fn pop_front<T: Value, N: Unsigned>(list: &List<T, N>, n: usize) -> List<T, N> {
    let mut list_popped = list.clone();
    list_popped.pop_front(n).unwrap();
    list_popped
}

pub fn pop_front_list_u64(c: &mut Criterion) {
    let size = N;

    let base_list = List::<u64, C>::try_from_iter(0..size).unwrap();

    c.bench_with_input(
        BenchmarkId::new("pop_front_noop", size),
        &base_list,
        |b, list| {
            b.iter(|| pop_front(list, 0));
        },
    );
    // This is one of the worst cases because we can't reuse any nodes.
    c.bench_with_input(
        BenchmarkId::new("pop_front_3", size),
        &base_list,
        |b, list| {
            b.iter(|| pop_front(list, 3));
        },
    );
    // This should be a bit quicker because we are aligned to the packing factor and can copy whole
    // leaves.
    c.bench_with_input(
        BenchmarkId::new("pop_front_4", size),
        &base_list,
        |b, list| {
            b.iter(|| pop_front(list, 4));
        },
    );
    c.bench_with_input(
        BenchmarkId::new("pop_front_32", size),
        &base_list,
        |b, list| {
            b.iter(|| pop_front(list, 32));
        },
    );
    c.bench_with_input(
        BenchmarkId::new("pop_front_400k", size),
        &base_list,
        |b, list| {
            b.iter(|| pop_front(list, 400_000));
        },
    );
}

criterion_group!(benches, pop_front_list_u64);
criterion_main!(benches);
