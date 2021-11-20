/// Borrow function to help with implementing traits for `&'a mut T`.
#[inline(always)]
pub fn borrow_mut<'s, 'a, T>(v: &'s &'a mut T) -> &'s T {
    &*v
}

/// Compute ceil(log(n))
///
/// Smallest number of bits d so that n <= 2^d
pub fn int_log(n: usize) -> usize {
    match n.checked_next_power_of_two() {
        Some(x) => x.trailing_zeros() as usize,
        None => 8 * std::mem::size_of::<usize>(),
    }
}
