#![feature(try_trait_v2)]
use std::convert::Infallible;
use std::ops::{ControlFlow, FromResidual, Try};

pub fn map<T, U, F: FnOnce(T) -> U>(value: Option<T>, f: F) -> Option<U> {
    value.map(f)
}
pub fn is_none_or<T, F: FnOnce(T) -> bool>(value: Option<T>, f: F) -> bool {
    value.is_none_or(f)
}
pub fn is_some_and<T, F: FnOnce(T) -> bool>(value: Option<T>, f: F) -> bool {
    value.is_some_and(f)
}
pub fn map_or<T, U, F: FnOnce(T) -> U>(value: Option<T>, fallback: U, f: F) -> U {
    value.map_or(fallback, f)
}
pub fn unwrap_or_default<T: Default>(value: Option<T>) -> T {
    value.unwrap_or_default()
}
pub fn ok_or<T, E>(value: Option<T>, error: E) -> Result<T, E> {
    value.ok_or(error)
}
pub fn or<T>(value: Option<T>, fallback: Option<T>) -> Option<T> {
    value.or(fallback)
}
pub fn unzip<T, U>(value: Option<(T, U)>) -> (Option<T>, Option<U>) {
    value.unzip()
}
pub fn copied<T: Copy>(value: Option<&T>) -> Option<T> {
    value.copied()
}
pub fn cloned<T: Clone>(value: Option<&T>) -> Option<T> {
    value.cloned()
}
pub fn branch<T>(value: Option<T>) -> ControlFlow<Option<Infallible>, T> {
    value.branch()
}
pub fn from_residual<T>(value: Option<Infallible>) -> Option<T> {
    Option::<T>::from_residual(value)
}
