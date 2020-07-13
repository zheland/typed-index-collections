use core::borrow::Borrow;

#[cfg(any(feature = "alloc", feature = "std"))]
use alloc::string::String;

use crate::{TiSlice, TiVec};

/// Helper trait for [`[T]::concat`](../../std/primitive.slice.html#method.concat).
pub trait Concat<Item: ?Sized> {
    /// The resulting type after concatenation
    type Output;

    /// Implementation of [`[T]::concat`](../../std/primitive.slice.html#method.concat)
    fn concat(slice: &Self) -> Self::Output;
}

impl<K, V: Borrow<str>> Concat<str> for TiSlice<K, V> {
    type Output = String;

    fn concat(slice: &Self) -> Self::Output {
        slice.raw.concat()
    }
}

impl<K, T: Clone, V: Borrow<[T]>> Concat<T> for TiSlice<K, V> {
    type Output = TiVec<K, T>;

    fn concat(slice: &Self) -> Self::Output {
        slice.raw.concat().into()
    }
}
