use core::iter::FromIterator;

#[cfg(any(feature = "alloc", feature = "std"))]
use alloc::{boxed::Box, vec};

#[cfg(any(feature = "serde-alloc", feature = "serde-std"))]
use serde::de::{Deserialize, Deserializer};

use crate::{TiSlice, TiVec};

impl<K, V> From<Box<TiSlice<K, V>>> for Box<[V]> {
    fn from(slice: Box<TiSlice<K, V>>) -> Box<[V]> {
        let ptr = Box::into_raw(slice) as *mut [V];
        unsafe { Box::from_raw(ptr) }
    }
}

impl<K, V> From<Box<[V]>> for Box<TiSlice<K, V>> {
    fn from(slice: Box<[V]>) -> Box<TiSlice<K, V>> {
        let ptr = Box::into_raw(slice) as *mut TiSlice<K, V>;
        unsafe { Box::from_raw(ptr) }
    }
}

impl<K, V: Clone> Clone for Box<TiSlice<K, V>> {
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
    #[inline(always)]
    fn default() -> Self {
        TiVec::new().into()
    }
}

impl<K, V: Copy> From<&TiSlice<K, V>> for Box<TiSlice<K, V>> {
    fn from(slice: &TiSlice<K, V>) -> Box<TiSlice<K, V>> {
        Box::<[V]>::from(&slice.raw).into()
    }
}

impl<K, V> From<Box<TiSlice<K, V>>> for TiVec<K, V> {
    fn from(s: Box<TiSlice<K, V>>) -> TiVec<K, V> {
        s.into_vec()
    }
}

impl<K, V> From<TiVec<K, V>> for Box<TiSlice<K, V>> {
    fn from(v: TiVec<K, V>) -> Box<TiSlice<K, V>> {
        v.into_boxed_slice()
    }
}

impl<K, V> FromIterator<V> for Box<TiSlice<K, V>> {
    fn from_iter<T: IntoIterator<Item = V>>(iter: T) -> Self {
        iter.into_iter().collect::<TiVec<K, V>>().into_boxed_slice()
    }
}

#[cfg(any(feature = "serde-alloc", feature = "serde-std"))]
impl<'de, K, V: Deserialize<'de>> Deserialize<'de> for Box<TiSlice<K, V>> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Box::<[V]>::deserialize(deserializer).map(Into::into)
    }
}
