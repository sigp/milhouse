pub enum MaxIndexState {
    Empty,
    Known(usize),
}
impl MaxIndexState {
    pub fn record_insert(&mut self, index: usize) {
        match self {
            Self::Empty => *self = Self::Known(index),
            Self::Known(max_index) => *max_index = (*max_index).max(index),
        }
    }
}
pub fn take(action: &mut Option<(&mut MaxIndexState, usize)>) {
    if let Some((state, index)) = action.take() {
        state.record_insert(index);
    }
}
pub fn borrowed_try(value: Option<&mut u32>) -> Option<&mut u32> {
    let value = value?;
    Some(value)
}
pub fn fallback<'a>(value: Option<&'a u32>, other: &'a u32) -> Option<&'a u32> {
    value.or_else(|| Some(other))
}
pub struct Counter {
    count: u32,
}
impl Iterator for Counter {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        self.count += 1;
        Some(self.count)
    }
}
pub fn use_cloned(v: &[u32]) -> Option<u32> {
    v.iter().cloned().next()
}
pub fn into_iter(values: impl IntoIterator<Item = u32>) -> u32 {
    let mut sum = 0;
    for value in values {
        sum += value;
    }
    sum
}
pub fn callback<F: FnMut(u32)>(mut f: F) {
    f(3);
}
pub fn fnmut(value: &mut u32) {
    callback(|x| *value += x);
}
