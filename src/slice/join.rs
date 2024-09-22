use core::borrow::Borrow;

#[cfg(feature = "alloc")]
use alloc::string::String;

use crate::{TiSlice, TiVec};

/// Helper trait for [`[T]::join`](../../std/primitive.slice.html#method.join)
pub trait Join<Separator> {
    /// The resulting type after concatenation
    type Output;

    /// Implementation of [`[T]::join`](../../std/primitive.slice.html#method.join)
    fn join(slice: &Self, sep: Separator) -> Self::Output;
}

impl<K, V: Borrow<str>> Join<&str> for TiSlice<K, V> {
    type Output = String;

    #[inline]
    fn join(slice: &Self, sep: &str) -> Self::Output {
        slice.raw.join(sep)
    }
}

impl<K, T: Clone, V: Borrow<[T]>> Join<&T> for TiSlice<K, V> {
    type Output = TiVec<K, T>;

    #[inline]
    fn join(slice: &Self, sep: &T) -> Self::Output {
        slice.raw.join(sep).into()
    }
}

impl<K, T: Clone, V: Borrow<[T]>> Join<&[T]> for TiSlice<K, V> {
    type Output = TiVec<K, T>;

    #[inline]
    fn join(slice: &Self, sep: &[T]) -> Self::Output {
        slice.raw.join(sep).into()
    }
}
