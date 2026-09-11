// Diagnostic callers for the two branches of the September usize::pow body.
// These do not replace the original pow source-comparison root.
pub fn strict(value: usize, exponent: u32) -> usize {
    value.strict_pow(exponent)
}

pub fn wrapping(value: usize, exponent: u32) -> usize {
    value.wrapping_pow(exponent)
}
