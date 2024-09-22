use core::iter::FromIterator;
use core::mem::transmute;

#[cfg(any(feature = "alloc", feature = "std"))]
use alloc::{boxed::Box, vec};

#[cfg(any(feature = "serde-alloc", feature = "serde-std"))]
use serde::de::{Deserialize, Deserializer};

use crate::{TiSlice, TiVec};

impl<K, V> From<Box<TiSlice<K, V>>> for Box<[V]> {
    #[inline]
    fn from(slice: Box<TiSlice<K, V>>) -> Self {
        // SAFETY: `TiSlice<K, V>` is `repr(transparent)` over a `[V]` type.
        unsafe { transmute::<Box<TiSlice<K, V>>, Self>(slice) }
    }
}

impl<K, V> From<Box<[V]>> for Box<TiSlice<K, V>> {
    #[inline]
    fn from(slice: Box<[V]>) -> Self {
        // SAFETY: `TiSlice<K, V>` is `repr(transparent)` over a `[V]` type.
        unsafe { transmute::<Box<[V]>, Self>(slice) }
    }
}

impl<K, V: Clone> Clone for Box<TiSlice<K, V>> {
    #[inline]
    fn clone(&self) -> Self {
        self.to_vec().into_boxed_slice()
    }
}

impl<K, V> IntoIterator for Box<TiSlice<K, V>> {
    type Item = V;
    type IntoIter = vec::IntoIter<V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

impl<K, V> Default for Box<TiSlice<K, V>> {
    #[inline]
    fn default() -> Self {
        TiVec::new().into()
    }
}

impl<K, V: Copy> From<&TiSlice<K, V>> for Box<TiSlice<K, V>> {
    #[inline]
    fn from(slice: &TiSlice<K, V>) -> Self {
        Box::<[V]>::from(&slice.raw).into()
    }
}

impl<K, V> From<Box<TiSlice<K, V>>> for TiVec<K, V> {
    #[inline]
    fn from(s: Box<TiSlice<K, V>>) -> Self {
        s.into_vec()
    }
}

impl<K, V> From<TiVec<K, V>> for Box<TiSlice<K, V>> {
    #[inline]
    fn from(v: TiVec<K, V>) -> Self {
        v.into_boxed_slice()
    }
}

impl<K, V> FromIterator<V> for Box<TiSlice<K, V>> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = V>>(iter: T) -> Self {
        iter.into_iter().collect::<TiVec<K, V>>().into_boxed_slice()
    }
}

#[cfg(any(feature = "serde-alloc", feature = "serde-std"))]
impl<'de, K, V: Deserialize<'de>> Deserialize<'de> for Box<TiSlice<K, V>> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Box::<[V]>::deserialize(deserializer).map(Into::into)
    }
}
