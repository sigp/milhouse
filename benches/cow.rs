use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use milhouse::List;
use std::hint::black_box;

type Capacity = typenum::U1048576;

const LEN: usize = 16_384;
const INDEX: usize = LEN / 2;

fn bench_cow(c: &mut Criterion) {
    let base = List::<u64, Capacity>::try_from_iter(0..LEN as u64).unwrap();
    let mut group = c.benchmark_group("cow");

    let mut list = base.clone();
    group.bench_function("get_backing", |b| {
        b.iter(|| {
            let cow = black_box(&mut list).get_cow(black_box(INDEX)).unwrap();
            black_box(*cow)
        });
    });

    let mut list = base.clone();
    *list.get_mut(INDEX).unwrap() = u64::MAX;
    group.bench_function("get_updated", |b| {
        b.iter(|| {
            let cow = black_box(&mut list).get_cow(black_box(INDEX)).unwrap();
            black_box(*cow)
        });
    });

    group.bench_function("into_mut_backing", |b| {
        b.iter_batched_ref(
            || base.clone(),
            |list| {
                let cow = black_box(list).get_cow(black_box(INDEX)).unwrap();
                *cow.into_mut().unwrap() = black_box(u64::MAX);
            },
            BatchSize::SmallInput,
        );
    });

    let mut list = base.clone();
    *list.get_mut(INDEX).unwrap() = u64::MAX;
    group.bench_function("into_mut_updated", |b| {
        b.iter(|| {
            let cow = black_box(&mut list).get_cow(black_box(INDEX)).unwrap();
            *cow.into_mut().unwrap() = black_box(0);
        });
    });

    let mut list = base.clone();
    group.bench_with_input(BenchmarkId::new("iter_read", LEN), &LEN, |b, _| {
        b.iter(|| {
            let mut sum = 0u64;
            let mut iter = black_box(&mut list).iter_cow();
            while let Some((_, cow)) = iter.next_cow() {
                sum = black_box(sum.wrapping_add(*cow));
            }
            black_box(sum)
        });
    });

    group.bench_with_input(BenchmarkId::new("iter_mut", LEN), &LEN, |b, _| {
        b.iter_batched_ref(
            || base.clone(),
            |list| {
                let mut iter = black_box(list).iter_cow();
                while let Some((_, cow)) = iter.next_cow() {
                    *cow.into_mut().unwrap() = black_box(u64::MAX);
                }
            },
            BatchSize::LargeInput,
        );
    });

    group.finish();
}

criterion_group!(benches, bench_cow);
criterion_main!(benches);
