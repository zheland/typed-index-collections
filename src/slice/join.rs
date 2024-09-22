use core::borrow::Borrow;

use alloc::string::String;

use crate::{TiSlice, TiVec};

/// A helper trait for [`TiSlice::join`](crate::TiSlice#method.join)
pub trait Join<Separator> {
    /// The resulting type after concatenation
    type Output;

    /// Implementation of [`TiSlice::join`](crate::TiSlice#method.join)
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
