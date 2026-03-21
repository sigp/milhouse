use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use milhouse::List;

type C = typenum::U1099511627776;
const N: usize = 800_000;

fn with_pending_updates(base: &List<u64, C>, indices: &[usize]) -> List<u64, C> {
    let mut list = base.clone();
    for &index in indices {
        *list.get_cow(index).unwrap().make_mut().unwrap() = (index as u64) + 1_000_000_000;
    }
    list
}

pub fn apply_updates(c: &mut Criterion) {
    let base = List::<u64, C>::try_from_iter((0..N).map(|index| index as u64)).unwrap();
    let sparse_two = with_pending_updates(&base, &[17, N - 3]);
    let sparse_eight =
        with_pending_updates(&base, &[3, 29, 511, 4097, 65_537, 262_144, 524_287, N - 1]);
    let dense_window = with_pending_updates(&base, &(N / 2..N / 2 + 512).collect::<Vec<_>>());

    let mut group = c.benchmark_group("apply_updates");
    for (name, pending) in [
        ("sparse_two", sparse_two),
        ("sparse_eight", sparse_eight),
        ("dense_window_512", dense_window),
    ] {
        group.bench_with_input(BenchmarkId::new(name, N), &pending, |b, list| {
            b.iter_batched(
                || list.clone(),
                |mut pending| pending.apply_updates().unwrap(),
                BatchSize::LargeInput,
            );
        });
    }
    group.finish();
}

criterion_group!(benches, apply_updates);
criterion_main!(benches);
