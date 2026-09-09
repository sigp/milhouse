pub fn take<T: Default>(place: &mut T) -> T {
    std::mem::take(place)
}
pub fn div_ceil(value: usize, divisor: usize) -> usize {
    value.div_ceil(divisor)
}
