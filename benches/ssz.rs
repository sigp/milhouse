use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use milhouse::{List, Value, Vector};
use ssz::{Decode, Encode};
use ssz_types::VariableList;
use typenum::Unsigned;

type C = typenum::U1099511627776;
type D = typenum::U1000000;
const N: u64 = 1_000_000;

#[inline]
fn encode_list<T: Value, N: Unsigned>(l1: &List<T, N>) -> Vec<u8> {
    l1.as_ssz_bytes()
}

#[inline]
fn encode_decode_list<T: Value, N: Unsigned>(l1: &List<T, N>) -> List<T, N> {
    let bytes = l1.as_ssz_bytes();

    List::from_ssz_bytes(&bytes).unwrap()
}

#[inline]
fn encode_vector<T: Value, N: Unsigned>(v1: &Vector<T, N>) -> Vec<u8> {
    v1.as_ssz_bytes()
}

#[inline]
fn encode_decode_vector<T: Value, N: Unsigned>(v1: &Vector<T, N>) -> Vector<T, N> {
    let bytes = v1.as_ssz_bytes();

    Vector::from_ssz_bytes(&bytes).unwrap()
}

#[inline]
fn encode_variable_list<T: Value, N: Unsigned>(l1: &VariableList<T, N>) -> Vec<u8> {
    l1.as_ssz_bytes()
}

#[inline]
fn encode_decode_variable_list<T: Value + 'static, N: Unsigned>(
    l1: &VariableList<T, N>,
) -> VariableList<T, N> {
    let bytes = l1.as_ssz_bytes();

    VariableList::from_ssz_bytes(&bytes).unwrap()
}

pub fn ssz(c: &mut Criterion) {
    let size = N;

    let list = List::<u64, C>::try_from_iter(0..size).unwrap();
    let vector = Vector::<u64, D>::try_from_iter(0..size).unwrap();
    let variable_list = VariableList::<u64, C>::new((0..size).collect()).unwrap();

    c.bench_with_input(BenchmarkId::new("ssz_encode_list", size), &list, |b, l1| {
        b.iter(|| encode_list(l1));
    });

    c.bench_with_input(
        BenchmarkId::new("ssz_encode_decode_list", size),
        &list,
        |b, l1| {
            b.iter(|| encode_decode_list(l1));
        },
    );

    c.bench_with_input(
        BenchmarkId::new("ssz_encode_vector", size),
        &vector,
        |b, v1| {
            b.iter(|| encode_vector(v1));
        },
    );

    c.bench_with_input(
        BenchmarkId::new("ssz_encode_decode_vector", size),
        &vector,
        |b, v1| {
            b.iter(|| encode_decode_vector(v1));
        },
    );

    // Test `VariableList` as a point of comparison.
    c.bench_with_input(
        BenchmarkId::new("ssz_encode_variable_list", size),
        &variable_list,
        |b, l1| {
            b.iter(|| encode_variable_list(l1));
        },
    );

    // Test `VariableList` as a point of comparison.
    c.bench_with_input(
        BenchmarkId::new("ssz_encode_decode_variable_list", size),
        &variable_list,
        |b, l1| {
            b.iter(|| encode_decode_variable_list(l1));
        },
    );
}

criterion_group!(benches, ssz);
criterion_main!(benches);
