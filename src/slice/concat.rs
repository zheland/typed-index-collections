use core::borrow::Borrow;

use alloc::string::String;

use crate::{TiSlice, TiVec};

/// A helper trait for [`TiSlice::concat`](crate::TiSlice#method.concat).
pub trait Concat<Item: ?Sized> {
    /// The resulting type after concatenation
    type Output;

    /// Implementation of [`TiSlice::concat`](crate::TiSlice#method.concat)
    fn concat(slice: &Self) -> Self::Output;
}

impl<K, V: Borrow<str>> Concat<str> for TiSlice<K, V> {
    type Output = String;

    #[inline]
    fn concat(slice: &Self) -> Self::Output {
        slice.raw.concat()
    }
}

impl<K, T: Clone, V: Borrow<[T]>> Concat<T> for TiSlice<K, V> {
    type Output = TiVec<K, T>;

    #[inline]
    fn concat(slice: &Self) -> Self::Output {
        slice.raw.concat().into()
    }
}
