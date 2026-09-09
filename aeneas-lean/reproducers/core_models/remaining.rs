// Diagnostic callers for numeric model boundaries. These are not proof roots
// of the passing core audit; see README.md for the extraction commands.
pub fn trailing_zeros(value: usize) -> u32 {
    value.trailing_zeros()
}

pub fn pow(value: usize, exponent: u32) -> usize {
    value.pow(exponent)
}

pub fn checked_next_power_of_two(value: usize) -> Option<usize> {
    value.checked_next_power_of_two()
}

pub fn checked_pow(value: u128, exponent: u32) -> Option<u128> {
    value.checked_pow(exponent)
}

pub fn saturating_mul(value: u128, other: u128) -> u128 {
    value.saturating_mul(other)
}
