use core::{iter, ops};

use crate::TiSlice;

/// An iterator over all key-value pairs.
///
/// This struct is created by the [`TiSlice::iter_enumerated`],
/// [`TiSlice::iter_mut_enumerated`] and [`TiVec::drain_enumerated`] methods.
///
/// [`TiSlice::iter_enumerated`]: struct.TiSlice.html#method.iter_enumerated
/// [`TiSlice::iter_mut_enumerated`]: struct.TiSlice.html#method.iter_mut_enumerated
/// [`TiVec::drain_enumerated`]: struct.TiVec.html#method.drain_enumerated
pub type TiEnumerated<I, K, V> = iter::Map<iter::Enumerate<I>, fn((usize, V)) -> (K, V)>;

/// An iterator over all keys.
///
/// This struct is created by the [`TiSlice::keys`] method.
///
/// [`TiSlice::keys`]: struct.TiSlice.html#method.keys
pub type TiSliceKeys<K> = iter::Map<ops::Range<usize>, fn(usize) -> K>;

/// An iterator wrapper for iterators that yields [`TiSlice`] subslice
/// references.
///
/// [`TiSlice`]: struct.TiSlice.html
pub type TiSliceRefMap<Iter, K, V> = iter::Map<Iter, fn(&[V]) -> &TiSlice<K, V>>;

/// An iterator wrapper for iterators that yields [`TiSlice`] subslice mutable
/// references.
///
/// [`TiSlice`]: struct.TiSlice.html
pub type TiSliceMutMap<Iter, K, V> = iter::Map<Iter, fn(&mut [V]) -> &mut TiSlice<K, V>>;
