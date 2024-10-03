#[cfg(feature = "alloc")]
mod boxed;

#[cfg(feature = "alloc")]
mod concat;

#[cfg(feature = "alloc")]
mod join;

mod slice_index;

#[cfg(feature = "alloc")]
use alloc::borrow::{Cow, ToOwned};
#[cfg(feature = "alloc")]
use alloc::boxed::Box;
#[cfg(feature = "std")]
use alloc::string::String;
#[cfg(feature = "std")]
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ops::{Index, IndexMut, Range};
use core::slice::{
    ChunkBy, ChunkByMut, Chunks, ChunksExact, ChunksExactMut, ChunksMut, EscapeAscii, Iter,
    IterMut, RChunks, RChunksExact, RChunksExactMut, RChunksMut, RSplit, RSplitMut, RSplitN,
    RSplitNMut, Split, SplitInclusive, SplitInclusiveMut, SplitMut, SplitN, SplitNMut, Windows,
};
use core::str::Utf8Chunks;
#[cfg(feature = "std")]
use std::io::{BufRead, IoSlice, IoSliceMut, Read, Result as IoResult, Write};

#[cfg(feature = "alloc")]
pub use concat::Concat;
#[cfg(feature = "alloc")]
pub use join::Join;
#[cfg(feature = "serde")]
use serde::ser::{Serialize, Serializer};
pub use slice_index::TiSliceIndex;

#[cfg(feature = "alloc")]
use crate::TiVec;
use crate::{TiEnumerated, TiRangeBounds, TiSliceKeys, TiSliceMutMap, TiSliceRefMap};

/// A dynamically-sized view into a contiguous sequence of `T`
/// that only accepts keys of the type `K`.
///
/// `TiSlice<K, V>` is a wrapper around Rust primitive type [`slice`].
/// The struct mirrors the stable API of Rust [`slice`]
/// and forwards to it as much as possible.
///
/// `TiSlice<K, V>` uses `K` instead of `usize` for element indices.
/// It also uses [`Range`], [`RangeTo`], [`RangeFrom`], [`RangeInclusive`] and
/// [`RangeToInclusive`] range types with `K` indices for `get`-methods and
/// index expressions. The [`RangeFull`] trait is not currently supported.
///
/// `TiSlice<K, V>` require the index to implement
/// [`From<usize>`][`From`] and [`Into<usize>`][`Into`] traits.
/// Their implementation can be easily done
/// with [`derive_more`] crate and `#[derive(From, Into)]`.
///
/// There are zero-cost conversions available between types and references:
/// - [`&[V]`][`slice`] and `&TiSlice<K, V>` with [`AsRef`],
/// - [`&mut [V]`][`slice`] and `&mut TiSlice<K, V>` with [`AsMut`],
/// - [`Box<[V]>`][`Box`] and `Box<TiSlice<K, V>>` with [`From`] and [`Into`].
///
/// Added methods:
/// - [`from_ref`] - Converts a [`&[V]`][`slice`] into a `&TiSlice<K, V>`.
/// - [`from_mut`] - Converts a [`&mut [V]`][`slice`] into a `&mut TiSlice<K,
///   V>`.
/// - [`keys`] - Returns an iterator over all keys.
/// - [`next_key`] - Returns the index of the next slice element to be appended
///   and at the same time number of elements in the slice of type `K`.
/// - [`first_key`] - Returns the first slice element index of type `K`, or
///   `None` if the slice is empty.
/// - [`first_key_value`] - Returns the first slice element index of type `K`
///   and the element itself, or `None` if the slice is empty.
/// - [`first_key_value_mut`] - Returns the first slice element index of type
///   `K` and a mutable reference to the element itself, or `None` if the slice
///   is empty.
/// - [`last_key`] - Returns the last slice element index of type `K`, or `None`
///   if the slice is empty.
/// - [`last_key_value`] - Returns the last slice element index of type `K` and
///   the element itself, or `None` if the slice is empty.
/// - [`last_key_value_mut`] - Returns the last slice element index of type `K`
///   and a mutable reference to the element itself, or `None` if the slice is
///   empty.
/// - [`iter_enumerated`] - Returns an iterator over all key-value pairs. It
///   acts like `self.iter().enumerate()`, but use `K` instead of `usize` for
///   iteration indices.
/// - [`iter_mut_enumerated`] - Returns an iterator over all key-value pairs,
///   with mutable references to the values. It acts like
///   `self.iter_mut().enumerate()`, but use `K` instead of `usize` for
///   iteration indices.
/// - [`position`] - Searches for an element in an iterator, returning its index
///   of type `K`. It acts like `self.iter().position(...)`, but instead of
///   `usize` it returns index of type `K`.
/// - [`rposition`] - Searches for an element in an iterator from the right,
///   returning its index of type `K`. It acts like
///   `self.iter().rposition(...)`, but instead of `usize` it returns index of
///   type `K`.
///
/// # Example
///
/// ```
/// use derive_more::{From, Into};
/// use typed_index_collections::TiSlice;
///
/// #[derive(From, Into)]
/// struct FooId(usize);
///
/// let mut foos_raw = [1, 2, 5, 8];
/// let foos: &mut TiSlice<FooId, usize> = TiSlice::from_mut(&mut foos_raw);
/// foos[FooId(2)] = 4;
/// assert_eq!(foos[FooId(2)], 4);
/// ```
///
/// [`from_ref`]: #method.from_ref
/// [`from_mut`]: #method.from_mut
/// [`keys`]: #method.keys
/// [`next_key`]: #method.next_key
/// [`first_key`]: #method.first_key
/// [`first_key_value`]: #method.first_key_value
/// [`first_key_value_mut`]: #method.first_key_value_mut
/// [`last_key`]: #method.last_key
/// [`last_key_value`]: #method.last_key_value
/// [`last_key_value_mut`]: #method.last_key_value_mut
/// [`iter_enumerated`]: #method.iter_enumerated
/// [`iter_mut_enumerated`]: #method.iter_mut_enumerated
/// [`position`]: #method.position
/// [`rposition`]: #method.rposition
/// [`slice`]: https://doc.rust-lang.org/std/primitive.slice.html
/// [`From`]: https://doc.rust-lang.org/std/convert/trait.From.html
/// [`Into`]: https://doc.rust-lang.org/std/convert/trait.Into.html
/// [`AsRef`]: https://doc.rust-lang.org/std/convert/trait.AsRef.html
/// [`AsMut`]: https://doc.rust-lang.org/std/convert/trait.AsMut.html
/// [`Box`]: https://doc.rust-lang.org/std/boxed/struct.Box.html
/// [`Range`]: https://doc.rust-lang.org/std/ops/struct.Range.html
/// [`RangeTo`]: https://doc.rust-lang.org/std/ops/struct.RangeTo.html
/// [`RangeFrom`]: https://doc.rust-lang.org/std/ops/struct.RangeFrom.html
/// [`RangeInclusive`]: https://doc.rust-lang.org/std/ops/struct.RangeInclusive.html
/// [`RangeToInclusive`]: https://doc.rust-lang.org/std/ops/struct.RangeToInclusive.html
/// [`RangeFull`]: https://doc.rust-lang.org/std/ops/struct.RangeFull.html
/// [`derive_more`]: https://crates.io/crates/derive_more
#[repr(transparent)]
pub struct TiSlice<K, V> {
    /// Tied slice index type
    ///
    /// `fn(T) -> T` is *[PhantomData pattern][phantomdata patterns]*
    /// used to relax auto trait implementations bounds for
    /// [`Send`], [`Sync`], [`Unpin`], [`UnwindSafe`] and [`RefUnwindSafe`].
    ///
    /// Derive attribute is not used for trait implementations because it also
    /// requires the same trait implemented for K that is an unnecessary
    /// requirement.
    ///
    /// [phantomdata patterns]: https://doc.rust-lang.org/nomicon/phantom-data.html#table-of-phantomdata-patterns
    /// [`Send`]: https://doc.rust-lang.org/core/marker/trait.Send.html
    /// [`Sync`]: https://doc.rust-lang.org/core/marker/trait.Sync.html
    /// [`Unpin`]: https://doc.rust-lang.org/core/marker/trait.Unpin.html
    /// [`UnwindSafe`]: https://doc.rust-lang.org/core/std/panic/trait.UnwindSafe.html
    /// [`RefUnwindSafe`]: https://doc.rust-lang.org/core/std/panic/trait.RefUnwindSafe.html
    _marker: PhantomData<fn(K) -> K>,

    /// Raw slice property
    pub raw: [V],
}

impl<K, V> TiSlice<K, V> {
    /// Converts a `&[V]` into a `&TiSlice<K, V>`.
    ///
    /// # Example
    ///
    /// ```
    /// # use typed_index_collections::TiSlice;
    /// pub struct Id(usize);
    /// let slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[1, 2, 4]);
    /// ```
    #[expect(clippy::as_conversions, reason = "transparent over a `[V]` type")]
    #[inline]
    pub const fn from_ref(raw: &[V]) -> &Self {
        // SAFETY: `TiSlice<K, V>` is `repr(transparent)` over a `[V]` type.
        unsafe { &*(core::ptr::from_ref::<[V]>(raw) as *const Self) }
    }

    /// Converts a `&mut [V]` into a `&mut TiSlice<K, V>`.
    ///
    /// # Example
    ///
    /// ```
    /// # use typed_index_collections::TiSlice;
    /// pub struct Id(usize);
    /// let slice: &mut TiSlice<Id, usize> = TiSlice::from_mut(&mut [1, 2, 4]);
    /// ```
    #[expect(clippy::as_conversions, reason = "transparent over a `[V]` type")]
    #[inline]
    pub fn from_mut(raw: &mut [V]) -> &mut Self {
        // SAFETY: `TiSlice<K, V>` is `repr(transparent)` over a `[V]` type.
        unsafe { &mut *(core::ptr::from_mut::<[V]>(raw) as *mut Self) }
    }

    /// Returns the number of elements in the slice.
    ///
    /// See [`slice::len`] for more details.
    ///
    /// [`slice::len`]: https://doc.rust-lang.org/std/primitive.slice.html#method.len
    #[inline]
    pub const fn len(&self) -> usize {
        self.raw.len()
    }

    /// Returns the index of the next slice element to be appended
    /// and at the same time number of elements in the slice of type `K`.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Eq, Debug, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[1, 2, 4]);
    /// assert_eq!(slice.next_key(), Id(3));
    /// ```
    #[inline]
    pub fn next_key(&self) -> K
    where
        K: From<usize>,
    {
        self.raw.len().into()
    }

    /// Returns `true` if the slice has a length of 0.
    ///
    /// See [`slice::is_empty`] for more details.
    ///
    /// [`slice::is_empty`]: https://doc.rust-lang.org/std/primitive.slice.html#method.is_empty
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    /// Returns an iterator over all keys.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Debug, Eq, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[1, 2, 4]);
    /// let mut iterator = slice.keys();
    /// assert_eq!(iterator.next(), Some(Id(0)));
    /// assert_eq!(iterator.next(), Some(Id(1)));
    /// assert_eq!(iterator.next(), Some(Id(2)));
    /// assert_eq!(iterator.next(), None);
    /// ```
    #[inline]
    pub fn keys(&self) -> TiSliceKeys<K>
    where
        K: From<usize>,
    {
        (0..self.len()).map(Into::into)
    }

    /// Returns the first element of the slice, or `None` if it is empty.
    ///
    /// See [`slice::first`] for more details.
    ///
    /// [`slice::first`]: https://doc.rust-lang.org/std/primitive.slice.html#method.first
    #[inline]
    pub const fn first(&self) -> Option<&V> {
        self.raw.first()
    }

    /// Returns a mutable reference to the first element of the slice, or `None`
    /// if it is empty.
    ///
    /// See [`slice::first_mut`] for more details.
    ///
    /// [`slice::first_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.first_mut
    #[inline]
    pub fn first_mut(&mut self) -> Option<&mut V> {
        self.raw.first_mut()
    }

    /// Returns the first slice element index of type `K`, or `None` if the
    /// slice is empty.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Debug, Eq, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let empty_slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[]);
    /// let slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[1, 2, 4]);
    /// assert_eq!(empty_slice.first_key(), None);
    /// assert_eq!(slice.first_key(), Some(Id(0)));
    /// ```
    #[inline]
    pub fn first_key(&self) -> Option<K>
    where
        K: From<usize>,
    {
        if self.is_empty() {
            None
        } else {
            Some(0.into())
        }
    }

    /// Returns the first slice element index of type `K` and the element
    /// itself, or `None` if the slice is empty.
    ///
    /// See [`slice::first`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Debug, Eq, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let empty_slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[]);
    /// let slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[1, 2, 4]);
    /// assert_eq!(empty_slice.first_key_value(), None);
    /// assert_eq!(slice.first_key_value(), Some((Id(0), &1)));
    /// ```
    ///
    /// [`slice::first`]: https://doc.rust-lang.org/std/primitive.slice.html#method.first
    #[inline]
    pub fn first_key_value(&self) -> Option<(K, &V)>
    where
        K: From<usize>,
    {
        self.raw.first().map(|first| (0.into(), first))
    }

    /// Returns the first slice element index of type `K` and a mutable
    /// reference to the element itself, or `None` if the slice is empty.
    ///
    /// See [`slice::first_mut`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Debug, Eq, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let empty_slice: &mut TiSlice<Id, usize> = TiSlice::from_mut(&mut []);
    /// let mut array = [1, 2, 4];
    /// let slice: &mut TiSlice<Id, usize> = TiSlice::from_mut(&mut array);
    /// assert_eq!(empty_slice.first_key_value_mut(), None);
    /// assert_eq!(slice.first_key_value_mut(), Some((Id(0), &mut 1)));
    /// *slice.first_key_value_mut().unwrap().1 = 123;
    /// assert_eq!(slice.raw, [123, 2, 4]);
    /// ```
    ///
    /// [`slice::first_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.first_mut
    #[inline]
    pub fn first_key_value_mut(&mut self) -> Option<(K, &mut V)>
    where
        K: From<usize>,
    {
        self.raw.first_mut().map(|first| (0.into(), first))
    }

    /// Returns the first and all the rest of the elements of the slice, or
    /// `None` if it is empty.
    ///
    /// See [`slice::split_first`] for more details.
    ///
    /// [`slice::split_first`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_first
    #[inline]
    pub fn split_first(&self) -> Option<(&V, &Self)> {
        self.raw
            .split_first()
            .map(|(first, rest)| (first, rest.as_ref()))
    }

    /// Returns the first and all the rest of the elements of the slice, or
    /// `None` if it is empty.
    ///
    /// See [`slice::split_first_mut`] for more details.
    ///
    /// [`slice::split_first_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_first_mut
    #[inline]
    pub fn split_first_mut(&mut self) -> Option<(&mut V, &mut Self)> {
        self.raw
            .split_first_mut()
            .map(|(first, rest)| (first, rest.as_mut()))
    }

    /// Returns the last and all the rest of the elements of the slice, or
    /// `None` if it is empty.
    ///
    /// See [`slice::split_last`] for more details.
    ///
    /// [`slice::split_last`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_last
    #[inline]
    pub fn split_last(&self) -> Option<(&V, &Self)> {
        self.raw
            .split_last()
            .map(|(last, rest)| (last, rest.as_ref()))
    }

    /// Returns the last and all the rest of the elements of the slice, or
    /// `None` if it is empty.
    ///
    /// See [`slice::split_last_mut`] for more details.
    ///
    /// [`slice::split_last_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_last_mut
    #[inline]
    pub fn split_last_mut(&mut self) -> Option<(&mut V, &mut Self)> {
        self.raw
            .split_last_mut()
            .map(|(last, rest)| (last, rest.as_mut()))
    }

    /// Returns the last element of the slice of type `K`, or `None` if it is
    /// empty.
    ///
    /// See [`slice::last`] for more details.
    ///
    /// [`slice::last`]: https://doc.rust-lang.org/std/primitive.slice.html#method.last
    #[inline]
    pub const fn last(&self) -> Option<&V> {
        self.raw.last()
    }

    /// Returns a mutable reference to the last item in the slice.
    ///
    /// See [`slice::last_mut`] for more details.
    ///
    /// [`slice::last_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.last_mut
    #[inline]
    pub fn last_mut(&mut self) -> Option<&mut V> {
        self.raw.last_mut()
    }

    /// Returns the last slice element index of type `K`, or `None` if the slice
    /// is empty.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Debug, Eq, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let empty_slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[]);
    /// let slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[1, 2, 4]);
    /// assert_eq!(empty_slice.last_key(), None);
    /// assert_eq!(slice.last_key(), Some(Id(2)));
    /// ```
    #[inline]
    pub fn last_key(&self) -> Option<K>
    where
        K: From<usize>,
    {
        Some(self.len().checked_sub(1)?.into())
    }

    /// Returns the last slice element index of type `K` and the element itself,
    /// or `None` if the slice is empty.
    ///
    /// See [`slice::last`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Debug, Eq, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let empty_slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[]);
    /// let slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[1, 2, 4]);
    /// assert_eq!(empty_slice.last_key_value(), None);
    /// assert_eq!(slice.last_key_value(), Some((Id(2), &4)));
    /// ```
    ///
    /// [`slice::last`]: https://doc.rust-lang.org/std/primitive.slice.html#method.last
    #[expect(clippy::missing_panics_doc, reason = "should not panic")]
    #[inline]
    pub fn last_key_value(&self) -> Option<(K, &V)>
    where
        K: From<usize>,
    {
        let len = self.len();
        self.raw.last().map(|last| {
            (
                len.checked_sub(1).expect("unexpected overflow").into(),
                last,
            )
        })
    }

    /// Returns the last slice element index of type `K` and a mutable reference
    /// to the element itself, or `None` if the slice is empty.
    ///
    /// See [`slice::last_mut`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Debug, Eq, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let empty_slice: &mut TiSlice<Id, usize> = TiSlice::from_mut(&mut []);
    /// let mut array = [1, 2, 4];
    /// let slice: &mut TiSlice<Id, usize> = TiSlice::from_mut(&mut array);
    /// assert_eq!(empty_slice.last_key_value_mut(), None);
    /// assert_eq!(slice.last_key_value_mut(), Some((Id(2), &mut 4)));
    /// *slice.last_key_value_mut().unwrap().1 = 123;
    /// assert_eq!(slice.raw, [1, 2, 123]);
    /// ```
    ///
    /// [`slice::last_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.last_mut
    #[expect(clippy::missing_panics_doc, reason = "should not panic")]
    #[inline]
    pub fn last_key_value_mut(&mut self) -> Option<(K, &mut V)>
    where
        K: From<usize>,
    {
        let len = self.len();
        self.raw.last_mut().map(|last| {
            (
                len.checked_sub(1).expect("unexpected overflow").into(),
                last,
            )
        })
    }

    /// Returns a reference to an element or subslice
    /// depending on the type of index or `None` if the index is out of bounds.
    ///
    /// See [`slice::get`] for more details.
    ///
    /// [`slice::get`]: https://doc.rust-lang.org/std/primitive.slice.html#method.get
    #[inline]
    pub fn get<I>(&self, index: I) -> Option<&I::Output>
    where
        I: TiSliceIndex<K, V>,
    {
        index.get(self)
    }

    /// Returns a mutable reference to an element or subslice
    /// depending on the type of index or `None` if the index is out of bounds.
    ///
    /// See [`slice::get_mut`] for more details.
    ///
    /// [`slice::get_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.get_mut
    #[inline]
    pub fn get_mut<I>(&mut self, index: I) -> Option<&mut I::Output>
    where
        I: TiSliceIndex<K, V>,
    {
        index.get_mut(self)
    }

    /// Returns a reference to an element or subslice
    /// depending on the type of index, without doing bounds checking.
    ///
    /// See [`slice::get_unchecked`] for more details.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is
    /// *[undefined behavior]* even if the resulting reference is not used.
    /// For a safe alternative see [`get`].
    ///
    /// [`get`]: #method.get
    /// [`slice::get_unchecked`]: https://doc.rust-lang.org/std/primitive.slice.html#method.get_unchecked
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_unchecked<I>(&self, index: I) -> &I::Output
    where
        I: TiSliceIndex<K, V>,
    {
        index.get_unchecked(self)
    }

    /// Returns a mutable reference to an element or subslice
    /// depending on the type of index, without doing bounds checking.
    ///
    /// See [`slice::get_unchecked_mut`] for more details.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is
    /// *[undefined behavior]* even if the resulting reference is not used.
    /// For a safe alternative see [`get_mut`].
    ///
    /// [`get_mut`]: #method.get_mut
    /// [`slice::get_unchecked_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.get_unchecked_mut
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_unchecked_mut<I>(&mut self, index: I) -> &mut I::Output
    where
        I: TiSliceIndex<K, V>,
    {
        index.get_unchecked_mut(self)
    }

    /// Returns a raw pointer to the slice's buffer.
    ///
    /// See [`slice::as_ptr`] for more details.
    ///
    /// [`slice::as_ptr`]: https://doc.rust-lang.org/std/primitive.slice.html#method.as_ptr
    #[inline]
    pub const fn as_ptr(&self) -> *const V {
        self.raw.as_ptr()
    }

    /// Returns an unsafe mutable reference to the slice's buffer.
    ///
    /// See [`slice::as_mut_ptr`] for more details.
    ///
    /// [`slice::as_mut_ptr`]: https://doc.rust-lang.org/std/primitive.slice.html#method.as_mut_ptr
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut V {
        self.raw.as_mut_ptr()
    }

    /// Returns the two raw pointers spanning the slice.
    ///
    /// See [`slice::as_ptr_range`] for more details.
    ///
    /// [`slice::as_ptr_range`]: https://doc.rust-lang.org/std/primitive.slice.html#method.as_ptr_range
    #[inline]
    #[must_use]
    pub const fn as_ptr_range(&self) -> Range<*const V> {
        self.raw.as_ptr_range()
    }

    /// Returns the two unsafe mutable pointers spanning the slice.
    ///
    /// See [`slice::as_mut_ptr_range`] for more details.
    ///
    /// [`slice::as_mut_ptr_range`]: https://doc.rust-lang.org/std/primitive.slice.html#method.as_mut_ptr_range
    #[inline]
    #[must_use]
    pub fn as_mut_ptr_range(&mut self) -> Range<*mut V> {
        self.raw.as_mut_ptr_range()
    }

    /// Swaps two elements in the slice.
    ///
    /// See [`slice::swap`] for more details.
    ///
    /// [`slice::swap`]: https://doc.rust-lang.org/std/primitive.slice.html#method.swap
    #[inline]
    pub fn swap(&mut self, a: K, b: K)
    where
        usize: From<K>,
    {
        self.raw.swap(a.into(), b.into());
    }

    /// Reverses the order of elements in the slice, in place.
    ///
    /// See [`slice::reverse`] for more details.
    ///
    /// [`slice::reverse`]: https://doc.rust-lang.org/std/primitive.slice.html#method.reverse
    #[inline]
    pub fn reverse(&mut self) {
        self.raw.reverse();
    }

    /// Returns an iterator over the slice.
    ///
    /// See [`slice::iter`] for more details.
    ///
    /// [`slice::iter`]: https://doc.rust-lang.org/std/primitive.slice.html#method.iter
    #[inline]
    pub fn iter(&self) -> Iter<'_, V> {
        self.raw.iter()
    }

    /// Returns an iterator over all key-value pairs.
    ///
    /// It acts like `self.iter().enumerate()`,
    /// but use `K` instead of `usize` for iteration indices.
    ///
    /// See [`slice::iter`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Debug, Eq, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[1, 2, 4]);
    /// let mut iterator = slice.iter_enumerated();
    /// assert_eq!(iterator.next(), Some((Id(0), &1)));
    /// assert_eq!(iterator.next(), Some((Id(1), &2)));
    /// assert_eq!(iterator.next(), Some((Id(2), &4)));
    /// assert_eq!(iterator.next(), None);
    /// ```
    ///
    /// [`slice::iter`]: https://doc.rust-lang.org/std/primitive.slice.html#method.iter
    #[inline]
    pub fn iter_enumerated(&self) -> TiEnumerated<Iter<'_, V>, K, &V>
    where
        K: From<usize>,
    {
        self.raw
            .iter()
            .enumerate()
            .map(|(key, value)| (key.into(), value))
    }

    /// Returns an iterator that allows modifying each value.
    ///
    /// See [`slice::iter_mut`] for more details.
    ///
    /// [`slice::iter_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.iter_mut
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, V> {
        self.raw.iter_mut()
    }

    /// Returns an iterator over all key-value pairs, with mutable references to
    /// the values.
    ///
    /// It acts like `self.iter_mut().enumerate()`,
    /// but use `K` instead of `usize` for iteration indices.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Debug, Eq, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let mut array = [1, 2, 4];
    /// let slice: &mut TiSlice<Id, usize> = TiSlice::from_mut(&mut array);
    /// for (key, value) in slice.iter_mut_enumerated() {
    ///     *value += key.0;
    /// }
    /// assert_eq!(array, [1, 3, 6]);
    /// ```
    ///
    /// [`slice::iter_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.iter_mut
    #[inline]
    pub fn iter_mut_enumerated(&mut self) -> TiEnumerated<IterMut<'_, V>, K, &mut V>
    where
        K: From<usize>,
    {
        self.raw
            .iter_mut()
            .enumerate()
            .map(|(key, value)| (key.into(), value))
    }

    /// Searches for an element in an iterator, returning its index of type `K`.
    ///
    /// It acts like `self.iter().position(...)`,
    /// but instead of `usize` it returns index of type `K`.
    ///
    /// See [`slice::iter`] and [`Iterator::position`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Debug, Eq, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[1, 2, 4, 2, 1]);
    /// assert_eq!(slice.position(|&value| value == 1), Some(Id(0)));
    /// assert_eq!(slice.position(|&value| value == 2), Some(Id(1)));
    /// assert_eq!(slice.position(|&value| value == 3), None);
    /// assert_eq!(slice.position(|&value| value == 4), Some(Id(2)));
    /// ```
    ///
    /// [`slice::iter`]: https://doc.rust-lang.org/std/primitive.slice.html#method.iter
    /// [`Iterator::position`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.position
    #[inline]
    pub fn position<P>(&self, predicate: P) -> Option<K>
    where
        K: From<usize>,
        P: FnMut(&V) -> bool,
    {
        self.raw.iter().position(predicate).map(Into::into)
    }

    /// Searches for an element in an iterator from the right, returning its
    /// index of type `K`.
    ///
    /// It acts like `self.iter().rposition(...)`,
    /// but instead of `usize` it returns index of type `K`.
    ///
    /// See [`slice::iter`] and [`Iterator::rposition`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiSlice;
    /// #[derive(Debug, Eq, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[1, 2, 4, 2, 1]);
    /// assert_eq!(slice.rposition(|&value| value == 1), Some(Id(4)));
    /// assert_eq!(slice.rposition(|&value| value == 2), Some(Id(3)));
    /// assert_eq!(slice.rposition(|&value| value == 3), None);
    /// assert_eq!(slice.rposition(|&value| value == 4), Some(Id(2)));
    /// ```
    ///
    /// [`slice::iter`]: https://doc.rust-lang.org/std/primitive.slice.html#method.iter
    /// [`Iterator::rposition`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.rposition
    #[inline]
    pub fn rposition<P>(&self, predicate: P) -> Option<K>
    where
        K: From<usize>,
        P: FnMut(&V) -> bool,
    {
        self.raw.iter().rposition(predicate).map(Into::into)
    }

    /// Returns an iterator over all contiguous windows of length
    /// `size`. The windows overlap. If the slice is shorter than
    /// `size`, the iterator returns no values.
    ///
    /// See [`slice::windows`] for more details.
    ///
    /// [`slice::windows`]: https://doc.rust-lang.org/std/primitive.slice.html#method.windows
    #[inline]
    pub fn windows(&self, size: usize) -> TiSliceRefMap<Windows<'_, V>, K, V> {
        self.raw.windows(size).map(Self::from_ref)
    }

    /// Returns an iterator over `chunk_size` elements of the slice at a time,
    /// starting at the beginning of the slice.
    ///
    /// See [`slice::chunks`] for more details.
    ///
    /// [`slice::chunks`]: https://doc.rust-lang.org/std/primitive.slice.html#method.chunks
    #[inline]
    pub fn chunks(&self, chunk_size: usize) -> TiSliceRefMap<Chunks<'_, V>, K, V> {
        self.raw.chunks(chunk_size).map(Self::from_ref)
    }

    /// Returns an iterator over `chunk_size` elements of the slice at a time,
    /// starting at the beginning of the slice.
    ///
    /// See [`slice::chunks_mut`] for more details.
    ///
    /// [`slice::chunks_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.chunks_mut
    #[inline]
    pub fn chunks_mut(&mut self, chunk_size: usize) -> TiSliceMutMap<ChunksMut<'_, V>, K, V> {
        self.raw.chunks_mut(chunk_size).map(Self::from_mut)
    }

    /// Returns an iterator over `chunk_size` elements of the slice at a time,
    /// starting at the beginning of the slice.
    ///
    /// See [`slice::chunks_exact`] for more details.
    ///
    /// [`slice::chunks_exact`]: https://doc.rust-lang.org/std/primitive.slice.html#method.chunks_exact
    #[inline]
    pub fn chunks_exact(&self, chunk_size: usize) -> TiSliceRefMap<ChunksExact<'_, V>, K, V> {
        self.raw.chunks_exact(chunk_size).map(Self::from_ref)
    }

    /// Returns an iterator over `chunk_size` elements of the slice at a time,
    /// starting at the beginning of the slice.
    ///
    /// See [`slice::chunks_exact_mut`] for more details.
    ///
    /// [`slice::chunks_exact_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.chunks_exact_mut
    #[inline]
    pub fn chunks_exact_mut(
        &mut self,
        chunk_size: usize,
    ) -> TiSliceMutMap<ChunksExactMut<'_, V>, K, V> {
        self.raw.chunks_exact_mut(chunk_size).map(Self::from_mut)
    }

    /// Returns an iterator over `chunk_size` elements of the slice at a time,
    /// starting at the end of the slice.
    ///
    /// See [`slice::rchunks`] for more details.
    ///
    /// [`slice::rchunks`]: https://doc.rust-lang.org/std/primitive.slice.html#method.rchunks
    #[inline]
    pub fn rchunks(&self, chunk_size: usize) -> TiSliceRefMap<RChunks<'_, V>, K, V> {
        self.raw.rchunks(chunk_size).map(Self::from_ref)
    }

    /// Returns an iterator over `chunk_size` elements of the slice at a time,
    /// starting at the end of the slice.
    ///
    /// See [`slice::rchunks_mut`] for more details.
    ///
    /// [`slice::rchunks_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.rchunks_mut
    #[inline]
    pub fn rchunks_mut(&mut self, chunk_size: usize) -> TiSliceMutMap<RChunksMut<'_, V>, K, V> {
        self.raw.rchunks_mut(chunk_size).map(Self::from_mut)
    }

    /// Returns an iterator over `chunk_size` elements of the slice at a time,
    /// starting at the end of the slice.
    ///
    /// See [`slice::rchunks_exact`] for more details.
    ///
    /// [`slice::rchunks_exact`]: https://doc.rust-lang.org/std/primitive.slice.html#method.rchunks_exact
    #[inline]
    pub fn rchunks_exact(&self, chunk_size: usize) -> TiSliceRefMap<RChunksExact<'_, V>, K, V> {
        self.raw.rchunks_exact(chunk_size).map(Self::from_ref)
    }

    /// Returns an iterator over `chunk_size` elements of the slice at a time,
    /// starting at the end of the slice.
    ///
    /// See [`slice::rchunks_exact_mut`] for more details.
    ///
    /// [`slice::rchunks_exact_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.rchunks_exact_mut
    #[inline]
    pub fn rchunks_exact_mut(
        &mut self,
        chunk_size: usize,
    ) -> TiSliceMutMap<RChunksExactMut<'_, V>, K, V> {
        self.raw.rchunks_exact_mut(chunk_size).map(Self::from_mut)
    }

    /// Returns an iterator over the slice producing non-overlapping runs
    /// of elements using the predicate to separate them.
    ///
    /// See [`slice::chunk_by`] for more details.
    ///
    /// [`slice::chunk_by`]: https://doc.rust-lang.org/std/primitive.slice.html#method.chunk_by
    #[inline]
    pub fn chunk_by<F>(&self, pred: F) -> TiSliceRefMap<ChunkBy<'_, V, F>, K, V>
    where
        F: FnMut(&V, &V) -> bool,
    {
        self.raw.chunk_by(pred).map(Self::from_ref)
    }

    /// Returns an iterator over the slice producing non-overlapping mutable
    /// runs of elements using the predicate to separate them.
    ///
    /// See [`slice::chunk_by_mut`] for more details.
    ///
    /// [`slice::chunk_by_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.chunk_by_mut
    #[inline]
    pub fn chunk_by_mut<F>(&mut self, pred: F) -> TiSliceMutMap<ChunkByMut<'_, V, F>, K, V>
    where
        F: FnMut(&V, &V) -> bool,
    {
        self.raw.chunk_by_mut(pred).map(Self::from_mut)
    }

    /// Divides one slice into two at an index.
    ///
    /// See [`slice::split_at`] for more details.
    ///
    /// [`slice::split_at`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_at
    #[inline]
    pub fn split_at(&self, mid: K) -> (&Self, &Self)
    where
        usize: From<K>,
    {
        let (left, right) = self.raw.split_at(mid.into());
        (left.as_ref(), right.as_ref())
    }

    /// Divides one mutable slice into two at an index.
    ///
    /// See [`slice::split_at_mut`] for more details.
    ///
    /// [`slice::split_at_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_at_mut
    #[inline]
    pub fn split_at_mut(&mut self, mid: K) -> (&mut Self, &mut Self)
    where
        usize: From<K>,
    {
        let (left, right) = self.raw.split_at_mut(mid.into());
        (left.as_mut(), right.as_mut())
    }

    /// Divides one slice into two at an index, without doing bounds checking.
    ///
    /// See [`slice::split_at_unchecked`] for more details.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is
    /// *[undefined behavior]* even if the resulting reference is not used. The
    /// caller has to ensure that `0 <= mid <= self.len()`.
    ///
    /// [`slice::split_at_unchecked`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_at_unchecked
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    #[must_use]
    pub unsafe fn split_at_unchecked(&self, mid: K) -> (&Self, &Self)
    where
        usize: From<K>,
    {
        let (left, right) = self.raw.split_at_unchecked(mid.into());
        (left.as_ref(), right.as_ref())
    }

    /// Divides one mutable slice into two at an index, without doing bounds
    /// checking.
    ///
    /// See [`slice::split_at_mut_unchecked`] for more details.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is
    /// *[undefined behavior]* even if the resulting reference is not used. The
    /// caller has to ensure that `0 <= mid <= self.len()`.
    ///
    /// [`slice::split_at_mut_unchecked`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_at_mut_unchecked
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    #[must_use]
    pub unsafe fn split_at_mut_unchecked(&mut self, mid: K) -> (&mut Self, &mut Self)
    where
        usize: From<K>,
    {
        let (left, right) = self.raw.split_at_mut_unchecked(mid.into());
        (left.as_mut(), right.as_mut())
    }

    /// Divides one slice into two at an index, returning `None` if the slice is
    /// too short.
    ///
    /// See [`slice::split_at_checked`] for more details.
    ///
    /// [`slice::split_at_checked`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_at_checked
    #[inline]
    #[must_use]
    pub fn split_at_checked(&self, mid: K) -> Option<(&Self, &Self)>
    where
        usize: From<K>,
    {
        let (left, right) = self.raw.split_at_checked(mid.into())?;
        Some((left.as_ref(), right.as_ref()))
    }

    /// Divides one mutable slice into two at an index, returning `None` if the
    /// slice is too short.
    ///
    /// See [`slice::split_at_mut_checked`] for more details.
    ///
    /// [`slice::split_at_mut_checked`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_at_mut_checked
    #[inline]
    #[must_use]
    pub fn split_at_mut_checked(&mut self, mid: K) -> Option<(&mut Self, &mut Self)>
    where
        usize: From<K>,
    {
        let (left, right) = self.raw.split_at_mut_checked(mid.into())?;
        Some((left.as_mut(), right.as_mut()))
    }

    /// Returns an iterator over subslices separated by elements that match
    /// `pred`. The matched element is not contained in the subslices.
    ///
    /// See [`slice::split`] for more details.
    ///
    /// [`slice::split`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split
    #[inline]
    pub fn split<F>(&self, pred: F) -> TiSliceRefMap<Split<'_, V, F>, K, V>
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.split(pred).map(Self::from_ref)
    }

    /// Returns an iterator over mutable subslices separated by elements that
    /// match `pred`. The matched element is not contained in the subslices.
    ///
    /// See [`slice::split_mut`] for more details.
    ///
    /// [`slice::split_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_mut
    #[inline]
    pub fn split_mut<F>(&mut self, pred: F) -> TiSliceMutMap<SplitMut<'_, V, F>, K, V>
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.split_mut(pred).map(Self::from_mut)
    }

    /// Returns an iterator over subslices separated by elements that match
    /// `pred`. The matched element is contained in the end of the previous
    /// subslice as a terminator.
    ///
    /// See [`slice::split_inclusive`] for more details.
    ///
    /// [`slice::split_inclusive`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_inclusive
    #[inline]
    pub fn split_inclusive<F>(&self, pred: F) -> TiSliceRefMap<SplitInclusive<'_, V, F>, K, V>
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.split_inclusive(pred).map(Self::from_ref)
    }

    /// Returns an iterator over mutable subslices separated by elements that
    /// match `pred`. The matched element is contained in the previous
    /// subslice as a terminator.
    ///
    /// See [`slice::split_inclusive_mut`] for more details.
    ///
    /// [`slice::split_inclusive_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.split_inclusive_mut
    #[inline]
    pub fn split_inclusive_mut<F>(
        &mut self,
        pred: F,
    ) -> TiSliceMutMap<SplitInclusiveMut<'_, V, F>, K, V>
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.split_inclusive_mut(pred).map(Self::from_mut)
    }

    /// Returns an iterator over subslices separated by elements that match
    /// `pred`, starting at the end of the slice and working backwards.
    /// The matched element is not contained in the subslices.
    ///
    /// See [`slice::rsplit`] for more details.
    ///
    /// [`slice::rsplit`]: https://doc.rust-lang.org/std/primitive.slice.html#method.rsplit
    #[inline]
    pub fn rsplit<F>(&self, pred: F) -> TiSliceRefMap<RSplit<'_, V, F>, K, V>
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.rsplit(pred).map(Self::from_ref)
    }

    /// Returns an iterator over mutable subslices separated by elements that
    /// match `pred`, starting at the end of the slice and working
    /// backwards. The matched element is not contained in the subslices.
    ///
    /// See [`slice::rsplit_mut`] for more details.
    ///
    /// [`slice::rsplit_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.rsplit_mut
    #[inline]
    pub fn rsplit_mut<F>(&mut self, pred: F) -> TiSliceMutMap<RSplitMut<'_, V, F>, K, V>
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.rsplit_mut(pred).map(Self::from_mut)
    }

    /// Returns an iterator over subslices separated by elements that match
    /// `pred`, limited to returning at most `n` items. The matched element is
    /// not contained in the subslices.
    ///
    /// See [`slice::splitn`] for more details.
    ///
    /// [`slice::splitn`]: https://doc.rust-lang.org/std/primitive.slice.html#method.splitn
    #[inline]
    pub fn splitn<F>(&self, n: usize, pred: F) -> TiSliceRefMap<SplitN<'_, V, F>, K, V>
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.splitn(n, pred).map(Self::from_ref)
    }

    /// Returns an iterator over subslices separated by elements that match
    /// `pred`, limited to returning at most `n` items. The matched element is
    /// not contained in the subslices.
    ///
    /// See [`slice::splitn_mut`] for more details.
    ///
    /// [`slice::splitn_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.splitn_mut
    #[inline]
    pub fn splitn_mut<F>(&mut self, n: usize, pred: F) -> TiSliceMutMap<SplitNMut<'_, V, F>, K, V>
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.splitn_mut(n, pred).map(Self::from_mut)
    }

    /// Returns an iterator over subslices separated by elements that match
    /// `pred` limited to returning at most `n` items. This starts at the end of
    /// the slice and works backwards. The matched element is not contained in
    /// the subslices.
    ///
    /// See [`slice::rsplitn`] for more details.
    ///
    /// [`slice::rsplitn`]: https://doc.rust-lang.org/std/primitive.slice.html#method.rsplitn
    #[inline]
    pub fn rsplitn<F>(&self, n: usize, pred: F) -> TiSliceRefMap<RSplitN<'_, V, F>, K, V>
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.rsplitn(n, pred).map(Self::from_ref)
    }

    /// Returns an iterator over subslices separated by elements that match
    /// `pred` limited to returning at most `n` items. This starts at the end of
    /// the slice and works backwards. The matched element is not contained in
    /// the subslices.
    ///
    /// See [`slice::rsplitn_mut`] for more details.
    ///
    /// [`slice::rsplitn_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.rsplitn_mut
    #[inline]
    pub fn rsplitn_mut<F>(&mut self, n: usize, pred: F) -> TiSliceMutMap<RSplitNMut<'_, V, F>, K, V>
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.rsplitn_mut(n, pred).map(Self::from_mut)
    }

    /// Returns `true` if the slice contains an element with the given value.
    ///
    /// See [`slice::contains`] for more details.
    ///
    /// [`slice::contains`]: https://doc.rust-lang.org/std/primitive.slice.html#method.contains
    #[inline]
    pub fn contains(&self, x: &V) -> bool
    where
        V: PartialEq,
    {
        self.raw.contains(x)
    }

    /// Returns `true` if `needle` is a prefix of the slice.
    ///
    /// See [`slice::starts_with`] for more details.
    ///
    /// [`slice::starts_with`]: https://doc.rust-lang.org/std/primitive.slice.html#method.starts_with
    #[inline]
    pub fn starts_with(&self, needle: &Self) -> bool
    where
        V: PartialEq,
    {
        self.raw.starts_with(needle.as_ref())
    }

    /// Returns `true` if `needle` is a suffix of the slice.
    ///
    /// See [`slice::ends_with`] for more details.
    ///
    /// [`slice::ends_with`]: https://doc.rust-lang.org/std/primitive.slice.html#method.ends_with
    #[inline]
    pub fn ends_with(&self, needle: &Self) -> bool
    where
        V: PartialEq,
    {
        self.raw.ends_with(needle.as_ref())
    }

    /// Binary searches this sorted slice for a given element.
    ///
    /// See [`slice::binary_search`] for more details.
    ///
    /// [`slice::binary_search`]: https://doc.rust-lang.org/std/primitive.slice.html#method.binary_search
    #[expect(clippy::missing_errors_doc, reason = "missed in std docs")]
    #[inline]
    pub fn binary_search(&self, x: &V) -> Result<K, K>
    where
        V: Ord,
        K: From<usize>,
    {
        self.raw
            .binary_search(x)
            .map(Into::into)
            .map_err(Into::into)
    }

    /// Binary searches this sorted slice with a comparator function.
    ///
    /// See [`slice::binary_search_by`] for more details.
    ///
    /// [`slice::binary_search_by`]: https://doc.rust-lang.org/std/primitive.slice.html#method.binary_search_by
    #[expect(clippy::missing_errors_doc, reason = "missed in std docs")]
    #[inline]
    pub fn binary_search_by<'a, F>(&'a self, f: F) -> Result<K, K>
    where
        F: FnMut(&'a V) -> Ordering,
        K: From<usize>,
    {
        self.raw
            .binary_search_by(f)
            .map(Into::into)
            .map_err(Into::into)
    }

    /// Binary searches this sorted slice with a key extraction function.
    ///
    /// See [`slice::binary_search_by_key`] for more details.
    ///
    /// [`slice::binary_search_by_key`]: https://doc.rust-lang.org/std/primitive.slice.html#method.binary_search_by_key
    #[expect(clippy::missing_errors_doc, reason = "missed in std docs")]
    #[inline]
    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, f: F) -> Result<K, K>
    where
        F: FnMut(&'a V) -> B,
        B: Ord,
        K: From<usize>,
    {
        self.raw
            .binary_search_by_key(b, f)
            .map(Into::into)
            .map_err(Into::into)
    }

    /// Sorts the slice, but may not preserve the order of equal elements.
    ///
    /// See [`slice::sort_unstable`] for more details.
    ///
    /// [`slice::sort_unstable`]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort_unstable
    #[inline]
    pub fn sort_unstable(&mut self)
    where
        V: Ord,
    {
        self.raw.sort_unstable();
    }

    /// Sorts the slice with a comparator function, but may not preserve the
    /// order of equal elements.
    ///
    /// See [`slice::sort_unstable_by`] for more details.
    ///
    /// [`slice::sort_unstable_by`]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort_unstable_by
    #[inline]
    pub fn sort_unstable_by<F>(&mut self, compare: F)
    where
        F: FnMut(&V, &V) -> Ordering,
    {
        self.raw.sort_unstable_by(compare);
    }

    /// Sorts the slice with a key extraction function, but may not preserve the
    /// order of equal elements.
    ///
    /// See [`slice::sort_unstable_by_key`] for more details.
    ///
    /// [`slice::sort_unstable_by_key`]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort_unstable_by_key
    #[inline]
    pub fn sort_unstable_by_key<K2, F>(&mut self, f: F)
    where
        F: FnMut(&V) -> K2,
        K2: Ord,
    {
        self.raw.sort_unstable_by_key(f);
    }

    /// Reorder the slice such that the element at `index` after the reordering
    /// is at its final sorted position.
    ///
    /// See [`slice::select_nth_unstable`] for more details.
    ///
    /// # Panics
    ///
    /// Panics when `index >= len()`, meaning it always panics on empty slices.
    ///
    /// May panic if the implementation of [`Ord`] for `T` does not implement a
    /// [total order].
    ///
    /// [`slice::select_nth_unstable`]: https://doc.rust-lang.org/std/primitive.slice.html#method.select_nth_unstable
    #[inline]
    pub fn select_nth_unstable(&mut self, index: K) -> (&mut Self, &mut V, &mut Self)
    where
        usize: From<K>,
        V: Ord,
    {
        let (left, nth, right) = self.raw.select_nth_unstable(index.into());
        (Self::from_mut(left), nth, Self::from_mut(right))
    }

    /// Reorder the slice with a comparator function such that the element at
    /// `index` after the reordering is at its final sorted position.
    ///
    /// See [`slice::select_nth_unstable_by`] for more details.
    ///
    /// # Panics
    ///
    /// Panics when `index >= len()`, meaning it always panics on empty slices.
    ///
    /// May panic if `compare` does not implement a [total order].
    ///
    /// [`slice::select_nth_unstable_by`]: https://doc.rust-lang.org/std/primitive.slice.html#method.select_nth_unstable_by
    #[inline]
    pub fn select_nth_unstable_by<F>(
        &mut self,
        index: K,
        compare: F,
    ) -> (&mut Self, &mut V, &mut Self)
    where
        usize: From<K>,
        F: FnMut(&V, &V) -> Ordering,
    {
        let (left, nth, right) = self.raw.select_nth_unstable_by(index.into(), compare);
        (Self::from_mut(left), nth, Self::from_mut(right))
    }

    /// Reorder the slice with a key extraction function such that the element
    /// at `index` after the reordering is at its final sorted position.
    ///
    /// See [`slice::select_nth_unstable_by_key`] for more details.
    ///
    /// # Panics
    ///
    /// Panics when `index >= len()`, meaning it always panics on empty slices.
    ///
    /// May panic if `K: Ord` does not implement a total order.
    ///
    /// [`slice::select_nth_unstable_by_key`]: https://doc.rust-lang.org/std/primitive.slice.html#method.select_nth_unstable_by_key
    #[inline]
    pub fn select_nth_unstable_by_key<Key, F>(
        &mut self,
        index: K,
        f: F,
    ) -> (&mut Self, &mut V, &mut Self)
    where
        usize: From<K>,
        F: FnMut(&V) -> Key,
        Key: Ord,
    {
        let (left, nth, right) = self.raw.select_nth_unstable_by_key(index.into(), f);
        (Self::from_mut(left), nth, Self::from_mut(right))
    }

    /// Rotates the slice in-place such that the first `mid` elements of the
    /// slice move to the end while the last `self.next_key() - mid` elements
    /// move to the front. After calling `rotate_left`, the element
    /// previously at index `mid` will become the first element in the
    /// slice.
    ///
    /// See [`slice::rotate_left`] for more details.
    ///
    /// [`slice::rotate_left`]: https://doc.rust-lang.org/std/primitive.slice.html#method.rotate_left
    #[inline]
    pub fn rotate_left(&mut self, mid: K)
    where
        usize: From<K>,
    {
        self.raw.rotate_left(mid.into());
    }

    /// Rotates the slice in-place such that the first `self.next_key() - k`
    /// elements of the slice move to the end while the last `k` elements move
    /// to the front. After calling `rotate_right`, the element previously at
    /// index `self.next_key() - k` will become the first element in the slice.
    ///
    /// See [`slice::rotate_right`] for more details.
    ///
    /// [`slice::rotate_right`]: https://doc.rust-lang.org/std/primitive.slice.html#method.rotate_right
    #[inline]
    pub fn rotate_right(&mut self, k: K)
    where
        usize: From<K>,
    {
        self.raw.rotate_right(k.into());
    }

    /// Fills `self` with elements by cloning `value`.
    ///
    /// See [`slice::fill`] for more details.
    ///
    /// [`slice::fill`]: https://doc.rust-lang.org/std/primitive.slice.html#method.fill
    #[inline]
    pub fn fill(&mut self, value: V)
    where
        V: Clone,
    {
        self.raw.fill(value);
    }

    /// Fills `self` with elements returned by calling a closure repeatedly.
    ///
    /// See [`slice::fill_with`] for more details.
    ///
    /// [`slice::fill_with`]: https://doc.rust-lang.org/std/primitive.slice.html#method.fill_with
    #[inline]
    pub fn fill_with<F>(&mut self, f: F)
    where
        F: FnMut() -> V,
    {
        self.raw.fill_with(f);
    }

    /// Copies the elements from `src` into `self`.
    ///
    /// See [`slice::clone_from_slice`] for more details.
    ///
    /// [`slice::clone_from_slice`]: https://doc.rust-lang.org/std/primitive.slice.html#method.clone_from_slice
    #[inline]
    pub fn clone_from_slice(&mut self, src: &Self)
    where
        V: Clone,
    {
        self.raw.clone_from_slice(&src.raw);
    }

    /// Copies all elements from `src` into `self`, using a memcpy.
    ///
    /// See [`slice::copy_from_slice`] for more details.
    ///
    /// [`slice::copy_from_slice`]: https://doc.rust-lang.org/std/primitive.slice.html#method.copy_from_slice
    #[inline]
    pub fn copy_from_slice(&mut self, src: &Self)
    where
        V: Copy,
    {
        self.raw.copy_from_slice(&src.raw);
    }

    /// Copies elements from one part of the slice to another part of itself,
    /// using a memmove.
    ///
    /// See [`slice::copy_within`] for more details.
    ///
    /// [`slice::copy_within`]: https://doc.rust-lang.org/std/primitive.slice.html#method.copy_within
    #[inline]
    pub fn copy_within<R>(&mut self, src: R, dest: K)
    where
        R: TiRangeBounds<K>,
        V: Copy,
        usize: From<K>,
    {
        self.raw.copy_within(src.into_range(), dest.into());
    }

    /// Swaps all elements in `self` with those in `other`.
    ///
    ///
    /// See [`slice::swap_with_slice`] for more details.
    ///
    /// [`slice::swap_with_slice`]: https://doc.rust-lang.org/std/primitive.slice.html#method.swap_with_slice
    #[inline]
    pub fn swap_with_slice(&mut self, other: &mut Self) {
        self.raw.swap_with_slice(other.as_mut());
    }

    /// Transmute the slice to a slice of another type, ensuring alignment of
    /// the types is maintained.
    ///
    /// See [`slice::align_to`] for more details.
    ///
    /// # Safety
    ///
    /// This method is essentially a `transmute` with respect to the elements in
    /// the returned middle slice, so all the usual caveats pertaining to
    /// `transmute::<T, U>` also apply here.
    ///
    /// [`slice::align_to`]: https://doc.rust-lang.org/std/primitive.slice.html#method.align_to
    #[inline]
    pub unsafe fn align_to<U>(&self) -> (&Self, &TiSlice<K, U>, &Self) {
        let (first, mid, last) = self.raw.align_to();
        (first.as_ref(), mid.as_ref(), last.as_ref())
    }

    /// Transmute the slice to a slice of another type, ensuring alignment of
    /// the types is maintained.
    ///
    /// See [`slice::align_to_mut`] for more details.
    ///
    /// # Safety
    ///
    /// This method is essentially a `transmute` with respect to the elements in
    /// the returned middle slice, so all the usual caveats pertaining to
    /// `transmute::<T, U>` also apply here.
    ///
    /// [`slice::align_to_mut`]: https://doc.rust-lang.org/std/primitive.slice.html#method.align_to_mut
    #[inline]
    pub unsafe fn align_to_mut<U>(&mut self) -> (&mut Self, &mut TiSlice<K, U>, &mut Self) {
        let (first, mid, last) = self.raw.align_to_mut();
        (first.as_mut(), mid.as_mut(), last.as_mut())
    }

    /// Returns the index of the partition point according to the given
    /// predicate (the index of the first element of the second partition).
    ///
    /// See [`slice::partition_point`] for more details.
    ///
    /// [`slice::partition_point`]: https://doc.rust-lang.org/std/primitive.slice.html#method.partition_point
    #[inline]
    #[must_use]
    pub fn partition_point<P>(&self, pred: P) -> K
    where
        K: From<usize>,
        P: FnMut(&V) -> bool,
    {
        self.raw.partition_point(pred).into()
    }
}

impl<K> TiSlice<K, u8> {
    /// Checks if all bytes in this slice are within the ASCII range.
    ///
    /// See [`slice::is_ascii`] for more details.
    ///
    /// [`slice::is_ascii`]: https://doc.rust-lang.org/std/primitive.slice.html#method.is_ascii
    #[inline]
    #[must_use]
    pub const fn is_ascii(&self) -> bool {
        self.raw.is_ascii()
    }

    /// Checks that two slices are an ASCII case-insensitive match.
    ///
    /// See [`slice::eq_ignore_ascii_case`] for more details.
    ///
    /// [`slice::eq_ignore_ascii_case`]: https://doc.rust-lang.org/std/primitive.slice.html#method.eq_ignore_ascii_case
    #[inline]
    #[must_use]
    pub fn eq_ignore_ascii_case(&self, other: &Self) -> bool {
        self.raw.eq_ignore_ascii_case(other.as_ref())
    }

    /// Converts this slice to its ASCII upper case equivalent in-place.
    ///
    /// See [`slice::make_ascii_uppercase`] for more details.
    ///
    /// [`slice::make_ascii_uppercase`]: https://doc.rust-lang.org/std/primitive.slice.html#method.make_ascii_uppercase
    #[inline]
    pub fn make_ascii_uppercase(&mut self) {
        self.raw.make_ascii_uppercase();
    }

    /// Converts this slice to its ASCII lower case equivalent in-place.
    ///
    /// See [`slice::make_ascii_lowercase`] for more details.
    ///
    /// [`slice::make_ascii_lowercase`]: https://doc.rust-lang.org/std/primitive.slice.html#method.make_ascii_lowercase
    #[inline]
    pub fn make_ascii_lowercase(&mut self) {
        self.raw.make_ascii_lowercase();
    }

    /// Returns an iterator that produces an escaped version of this slice,
    /// treating it as an ASCII string.
    ///
    /// See [`slice::escape_ascii`] for more details.
    ///
    /// [`slice::escape_ascii`]: https://doc.rust-lang.org/std/primitive.slice.html#method.escape_ascii
    #[must_use = "this returns the escaped bytes as an iterator, without modifying the original"]
    #[inline]
    pub fn escape_ascii(&self) -> EscapeAscii<'_> {
        self.raw.escape_ascii()
    }

    /// Returns a byte slice with leading ASCII whitespace bytes removed.
    ///
    /// See [`slice::trim_ascii_start`] for more details.
    ///
    /// [`slice::trim_ascii_start`]: https://doc.rust-lang.org/std/primitive.slice.html#method.trim_ascii_start
    #[inline]
    #[must_use]
    pub const fn trim_ascii_start(&self) -> &Self {
        Self::from_ref(self.raw.trim_ascii_start())
    }

    /// Returns a byte slice with trailing ASCII whitespace bytes removed.
    ///
    /// See [`slice::trim_ascii_end`] for more details.
    ///
    /// [`slice::trim_ascii_end`]: https://doc.rust-lang.org/std/primitive.slice.html#method.trim_ascii_end
    #[inline]
    #[must_use]
    pub const fn trim_ascii_end(&self) -> &Self {
        Self::from_ref(self.raw.trim_ascii_end())
    }

    /// Returns a byte slice with leading and trailing ASCII whitespace bytes
    /// removed.
    ///
    /// See [`slice::trim_ascii`] for more details.
    ///
    /// [`slice::trim_ascii`]: https://doc.rust-lang.org/std/primitive.slice.html#method.trim_ascii
    #[inline]
    #[must_use]
    pub const fn trim_ascii(&self) -> &Self {
        Self::from_ref(self.raw.trim_ascii())
    }

    /// Creates an iterator over the contiguous valid UTF-8 ranges of this
    /// slice, and the non-UTF-8 fragments in between.
    ///
    /// See [`slice::utf8_chunks`] for more details.
    ///
    /// [`slice::utf8_chunks`]: https://doc.rust-lang.org/std/primitive.slice.html#method.utf8_chunks
    #[inline]
    pub fn utf8_chunks(&self) -> Utf8Chunks<'_> {
        self.raw.utf8_chunks()
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl<K, V> TiSlice<K, V> {
    /// Sorts the slice.
    ///
    /// See [`slice::sort`] for more details.
    ///
    /// [`slice::sort`]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort
    #[inline]
    pub fn sort(&mut self)
    where
        V: Ord,
    {
        self.raw.sort();
    }

    /// Sorts the slice with a comparator function.
    ///
    /// See [`slice::sort_by`] for more details.
    ///
    /// [`slice::sort_by`]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by
    #[inline]
    pub fn sort_by<F>(&mut self, compare: F)
    where
        F: FnMut(&V, &V) -> Ordering,
    {
        self.raw.sort_by(compare);
    }

    /// Sorts the slice with a key extraction function.
    ///
    /// See [`slice::sort_by_key`] for more details.
    ///
    /// [`slice::sort_by_key`]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_key
    #[inline]
    pub fn sort_by_key<K2, F>(&mut self, f: F)
    where
        F: FnMut(&V) -> K2,
        K2: Ord,
    {
        self.raw.sort_by_key(f);
    }

    /// Sorts the slice with a key extraction function.
    ///
    /// See [`slice::sort_by_cached_key`] for more details.
    ///
    /// [`slice::sort_by_cached_key`]: https://doc.rust-lang.org/std/primitive.slice.html#method.sort_by_cached_key
    #[inline]
    pub fn sort_by_cached_key<K2, F>(&mut self, f: F)
    where
        F: FnMut(&V) -> K2,
        K2: Ord,
    {
        self.raw.sort_by_cached_key(f);
    }

    /// Copies `self` into a new `TiVec`.
    ///
    /// See [`slice::to_vec`] for more details.
    ///
    /// [`slice::to_vec`]: https://doc.rust-lang.org/std/primitive.slice.html#method.to_vec
    #[inline]
    pub fn to_vec(&self) -> TiVec<K, V>
    where
        V: Clone,
    {
        self.raw.to_vec().into()
    }

    /// Converts `self` into a vector without clones or allocation.
    ///
    /// See [`slice::into_vec`] for more details.
    ///
    /// [`slice::into_vec`]: https://doc.rust-lang.org/std/primitive.slice.html#method.into_vec
    #[inline]
    #[must_use]
    pub fn into_vec(self: Box<Self>) -> TiVec<K, V> {
        Box::<[V]>::from(self).into_vec().into()
    }

    /// Creates a vector by repeating a slice `n` times.
    ///
    /// See [`slice::repeat`] for more details.
    ///
    /// [`slice::repeat`]: https://doc.rust-lang.org/std/primitive.slice.html#method.repeat
    #[inline]
    pub fn repeat(&self, n: usize) -> TiVec<K, V>
    where
        V: Copy,
    {
        self.raw.repeat(n).into()
    }

    /// Flattens a slice of `T` into a single value `Self::Output`.
    ///
    /// See [`slice::concat`] for more details.
    ///
    /// [`slice::concat`]: https://doc.rust-lang.org/std/primitive.slice.html#method.concat
    #[inline]
    pub fn concat<Item: ?Sized>(&self) -> <Self as Concat<Item>>::Output
    where
        Self: Concat<Item>,
    {
        Concat::concat(self)
    }

    /// Flattens a slice of `T` into a single value `Self::Output`, placing a
    /// given separator between each.
    ///
    /// See [`slice::join`] for more details.
    ///
    /// [`slice::join`]: https://doc.rust-lang.org/std/primitive.slice.html#method.join
    #[inline]
    pub fn join<Separator>(&self, sep: Separator) -> <Self as Join<Separator>>::Output
    where
        Self: Join<Separator>,
    {
        Join::join(self, sep)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl<K> TiSlice<K, u8> {
    /// Returns a vector containing a copy of this slice where each byte
    /// is mapped to its ASCII upper case equivalent.
    ///
    /// See [`slice::to_ascii_uppercase`] for more details.
    ///
    /// [`slice::to_ascii_uppercase`]: https://doc.rust-lang.org/std/primitive.slice.html#method.to_ascii_uppercase
    #[inline]
    #[must_use]
    pub fn to_ascii_uppercase(&self) -> TiVec<K, u8> {
        self.raw.to_ascii_uppercase().into()
    }

    /// Returns a vector containing a copy of this slice where each byte
    /// is mapped to its ASCII lower case equivalent.
    ///
    /// See [`slice::to_ascii_lowercase`] for more details.
    ///
    /// [`slice::to_ascii_lowercase`]: https://doc.rust-lang.org/std/primitive.slice.html#method.to_ascii_lowercase
    #[inline]
    #[must_use]
    pub fn to_ascii_lowercase(&self) -> TiVec<K, u8> {
        self.raw.to_ascii_lowercase().into()
    }
}

impl<K, V> fmt::Debug for TiSlice<K, V>
where
    K: fmt::Debug + From<usize>,
    V: fmt::Debug,
{
    #[allow(clippy::allow_attributes, reason = "rust-lang/rust#130021")]
    #[allow(
        clippy::missing_inline_in_public_items,
        reason = "use default inlining behavior"
    )]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter_enumerated()).finish()
    }
}

impl<K, V> AsRef<Self> for TiSlice<K, V> {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<K, V> AsMut<Self> for TiSlice<K, V> {
    #[inline]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<K, V> AsRef<[V]> for TiSlice<K, V> {
    #[inline]
    fn as_ref(&self) -> &[V] {
        &self.raw
    }
}

impl<K, V> AsMut<[V]> for TiSlice<K, V> {
    #[inline]
    fn as_mut(&mut self) -> &mut [V] {
        &mut self.raw
    }
}

impl<K, V> AsRef<TiSlice<K, V>> for [V] {
    #[inline]
    fn as_ref(&self) -> &TiSlice<K, V> {
        TiSlice::from_ref(self)
    }
}

impl<K, V> AsMut<TiSlice<K, V>> for [V] {
    #[inline]
    fn as_mut(&mut self) -> &mut TiSlice<K, V> {
        TiSlice::from_mut(self)
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl<'a, K, V: Clone> From<&'a TiSlice<K, V>> for Cow<'a, TiSlice<K, V>> {
    #[inline]
    fn from(value: &'a TiSlice<K, V>) -> Self {
        Cow::Borrowed(value)
    }
}

impl<K, V> Eq for TiSlice<K, V> where V: Eq {}

impl<K, A, B> PartialEq<TiSlice<K, B>> for TiSlice<K, A>
where
    A: PartialEq<B>,
{
    #[inline]
    fn eq(&self, other: &TiSlice<K, B>) -> bool {
        self.raw == other.raw
    }
}

impl<K, V> Ord for TiSlice<K, V>
where
    V: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.raw.cmp(&other.raw)
    }
}

impl<K, V> PartialOrd<Self> for TiSlice<K, V>
where
    V: PartialOrd<V>,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.raw.partial_cmp(&other.raw)
    }
}

impl<K, V> Hash for TiSlice<K, V>
where
    V: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

impl<K, V> Default for &TiSlice<K, V> {
    #[inline]
    fn default() -> Self {
        TiSlice::from_ref(&[])
    }
}

impl<K, V> Default for &mut TiSlice<K, V> {
    #[inline]
    fn default() -> Self {
        TiSlice::from_mut(&mut [])
    }
}

impl<I, K, V> Index<I> for TiSlice<K, V>
where
    I: TiSliceIndex<K, V>,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        index.index(self)
    }
}

impl<I, K, V> IndexMut<I> for TiSlice<K, V>
where
    I: TiSliceIndex<K, V>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        index.index_mut(self)
    }
}

impl<'a, K, V> IntoIterator for &'a TiSlice<K, V> {
    type Item = &'a V;
    type IntoIter = Iter<'a, V>;

    #[inline]
    fn into_iter(self) -> Iter<'a, V> {
        self.raw.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut TiSlice<K, V> {
    type Item = &'a mut V;
    type IntoIter = IterMut<'a, V>;

    #[inline]
    fn into_iter(self) -> IterMut<'a, V> {
        self.raw.iter_mut()
    }
}

/// Read is implemented for `&TiSlice<K, u8>` by copying from the slice.
///
/// Note that reading updates the slice to point to the yet unread part.
/// The slice will be empty when EOF is reached.
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<K> Read for &TiSlice<K, u8> {
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> IoResult<usize> {
        as_readable_byte_slice(self).read(buf)
    }

    #[inline]
    fn read_vectored(&mut self, bufs: &mut [IoSliceMut<'_>]) -> IoResult<usize> {
        as_readable_byte_slice(self).read_vectored(bufs)
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [u8]) -> IoResult<()> {
        as_readable_byte_slice(self).read_exact(buf)
    }

    #[inline]
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> IoResult<usize> {
        as_readable_byte_slice(self).read_to_end(buf)
    }

    #[inline]
    fn read_to_string(&mut self, buf: &mut String) -> IoResult<usize> {
        as_readable_byte_slice(self).read_to_string(buf)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<K> BufRead for &TiSlice<K, u8> {
    #[inline]
    fn fill_buf(&mut self) -> IoResult<&[u8]> {
        as_readable_byte_slice(self).fill_buf()
    }

    #[inline]
    fn consume(&mut self, amt: usize) {
        as_readable_byte_slice(self).consume(amt);
    }
}

/// Write is implemented for `&mut TiSlice<K, u8>` by copying into the slice,
/// overwriting its data.
///
/// Note that writing updates the slice to point to the yet unwritten part.
/// The slice will be empty when it has been completely overwritten.
///
/// If the number of bytes to be written exceeds the size of the slice, write
/// operations will return short writes: ultimately, `Ok(0)`; in this situation,
/// `write_all` returns an error of kind `ErrorKind::WriteZero`.
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<K> Write for &mut TiSlice<K, u8> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> IoResult<usize> {
        as_writable_byte_slice(self).write(buf)
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> IoResult<usize> {
        as_writable_byte_slice(self).write_vectored(bufs)
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> IoResult<()> {
        as_writable_byte_slice(self).write_all(buf)
    }

    #[inline]
    fn flush(&mut self) -> IoResult<()> {
        as_writable_byte_slice(self).flush()
    }
}

#[cfg(feature = "std")]
#[inline]
fn as_readable_byte_slice<'a, 'b, K>(value: &'a mut &'b TiSlice<K, u8>) -> &'a mut &'b [u8] {
    let ptr: *mut &TiSlice<K, u8> = core::ptr::from_mut::<&TiSlice<K, u8>>(value);
    let ptr: *mut &[u8] = ptr.cast();
    // SAFETY: `TiSlice<K, V>` is `repr(transparent)` over a `[V]` type.
    unsafe { &mut *ptr }
}

#[expect(clippy::mut_mut, reason = "can not avoid this cast")]
#[cfg(feature = "std")]
#[inline]
fn as_writable_byte_slice<'a, 'b, K>(
    value: &'a mut &'b mut TiSlice<K, u8>,
) -> &'a mut &'b mut [u8] {
    let ptr: *mut &mut TiSlice<K, u8> = core::ptr::from_mut::<&mut TiSlice<K, u8>>(value);
    let ptr: *mut &mut [u8] = ptr.cast();
    // SAFETY: `TiSlice<K, V>` is `repr(transparent)` over a `[V]` type.
    unsafe { &mut *ptr }
}

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
impl<K, V: Clone> ToOwned for TiSlice<K, V> {
    type Owned = TiVec<K, V>;

    #[inline]
    fn to_owned(&self) -> TiVec<K, V> {
        self.raw.to_owned().into()
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<K, V: Serialize> Serialize for TiSlice<K, V> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.raw.serialize(serializer)
    }
}

#[expect(
    dead_code,
    unused_imports,
    unused_mut,
    clippy::fallible_impl_from,
    clippy::into_iter_on_ref,
    clippy::too_many_lines,
    clippy::undocumented_unsafe_blocks,
    clippy::unwrap_used,
    clippy::zero_repeat_side_effects,
    reason = "okay in tests"
)]
#[cfg(test)]
mod test {
    #[cfg(feature = "alloc")]
    use alloc::borrow::{Cow, ToOwned};
    #[cfg(feature = "alloc")]
    use alloc::boxed::Box;
    #[cfg(feature = "std")]
    use alloc::string::{String, ToString};
    #[cfg(feature = "alloc")]
    use alloc::vec::Vec;
    use core::borrow::{Borrow, BorrowMut};
    use core::hash::{Hash, Hasher};
    use core::ops::Bound;
    #[cfg(feature = "std")]
    use std::hash::DefaultHasher;
    #[cfg(feature = "std")]
    use std::io::{BufRead, IoSlice, IoSliceMut, Read, Write};

    use crate::test_util::{CollectToVec, Id};
    use crate::TiSlice;

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct NonCopy<T>(pub T);

    #[test]
    fn test_slice_read_core_api_compatibility() {
        for v in [
            &[0_u32; 0][..],
            &[1],
            &[1, 1234],
            &[1, 2, 4],
            &[1, 5, 3, 2],
            &[1, 1, 9, 2, 4, 1, 12345, 12],
        ] {
            let mut cv = (v, TiSlice::from_ref(v));

            let mut mv = (v.to_vec(), v.to_vec());
            let mut mv = (mv.0.as_mut_slice(), TiSlice::from_mut(mv.1.as_mut_slice()));

            assert_eq_api!(cv, v => AsRef::<[_]>::as_ref(v));
            assert_eq_api!(mv, v => AsMut::<[_]>::as_mut(v));
            assert_eq_api!(cv, v => AsRef::<TiSlice<_, _>>::as_ref(v));
            assert_eq_api!(mv, v => AsMut::<TiSlice<_, _>>::as_mut(v));

            assert_eq_api!(cv, v => v.len());
            assert_eq_api!(cv, v => v.is_empty());
            assert_eq_api!(cv, v => v.first());
            assert_eq_api!(mv, v => v.first_mut());
            assert_eq_api!(cv, v => v.last());
            assert_eq_api!(mv, v => v.last_mut());
            assert_eq_api!(cv, v => v.split_first().into_std());
            assert_eq_api!(mv, v => v.split_first_mut().into_std());
            assert_eq_api!(cv, v => v.split_last().into_std());
            assert_eq_api!(mv, v => v.split_last_mut().into_std());

            assert_eq_api!(cv, v => v.as_ptr());
            assert_eq_api!(cv, v => v.as_ptr_range());
            if !v.is_empty() {
                assert_ne!(mv.0.as_mut_ptr(), mv.1.as_mut_ptr());
                assert_ne!(mv.0.as_mut_ptr_range(), mv.1.as_mut_ptr_range());
            }
            assert_eq!(
                mv.0.as_mut_ptr(),
                TiSlice::<Id, _>::from_mut(mv.0).as_mut_ptr()
            );
            assert_eq!(
                mv.0.as_mut_ptr_range(),
                TiSlice::<Id, _>::from_mut(mv.0).as_mut_ptr_range()
            );

            assert_eq_api!(cv, v => v == <&TheSlice<u32>>::default());
            assert_eq_api!(cv, v => v == <&mut TheSlice<u32>>::default());
            assert_eq_api!(cv, v => v.cmp([1, 1234][..].into_tic()));
            assert_eq_api!(cv, v => v.partial_cmp([1, 1234][..].into_tic()));

            assert_eq_api!(cv, v => v.get((Bound::Unbounded, Bound::Unbounded)).into_std());
            assert_eq_api!(mv, v => v.get_mut((Bound::Unbounded, Bound::Unbounded)).into_std());

            for i in 0..5_usize {
                assert_eq_api!(cv, v => v.get(i.into_tic()));
                assert_eq_api!(mv, v => v.get_mut(i.into_tic()));

                assert_eq_api!(cv, v => v.get(i.into_tic()..).into_std());
                assert_eq_api!(mv, v => v.get_mut(i.into_tic()..).into_std());

                assert_eq_api!(cv, v => v.get(..i.into_tic()).into_std());
                assert_eq_api!(mv, v => v.get_mut(..i.into_tic()).into_std());

                assert_eq_api!(cv, v => v.get(..=i.into_tic()).into_std());
                assert_eq_api!(mv, v => v.get_mut(..=i.into_tic()).into_std());

                let r = (Bound::Included(i), Bound::Unbounded);
                assert_eq_api!(cv, v => v.get(r.into_tic()).into_std());
                assert_eq_api!(mv, v => v.get_mut(r.into_tic()).into_std());

                let r = (Bound::Unbounded, Bound::Excluded(i));
                assert_eq_api!(cv, v => v.get(r.into_tic()).into_std());
                assert_eq_api!(mv, v => v.get_mut(r.into_tic()).into_std());

                let r = (Bound::Excluded(i), Bound::Unbounded);
                assert_eq_api!(cv, v => v.get(r.into_tic()).into_std());
                assert_eq_api!(mv, v => v.get_mut(r.into_tic()).into_std());

                let r = (Bound::Unbounded, Bound::Included(i));
                assert_eq_api!(cv, v => v.get(r.into_tic()).into_std());
                assert_eq_api!(mv, v => v.get_mut(r.into_tic()).into_std());
            }

            for i in 0..=v.len() {
                unsafe {
                    if i < v.len() {
                        assert_eq_api!(cv, v => v.get_unchecked(i.into_tic()));
                        assert_eq_api!(mv, v => v.get_unchecked_mut(i.into_tic()));
                        assert_eq_api!(cv, v => v[i.into_tic()]);
                        assert_eq_api!(mv, v => v[i.into_tic()] = v[i.into_tic()]);
                    }

                    assert_eq_api!(cv, v => v[i.into_tic()..].into_std());
                    assert_eq_api!(cv, v => v.get_unchecked(i.into_tic()..).into_std());
                    assert_eq_api!(mv, v => v.get_unchecked_mut(i.into_tic()..).into_std());

                    assert_eq_api!(cv, v => v[..i.into_tic()].into_std());
                    assert_eq_api!(cv, v => v.get_unchecked(..i.into_tic()).into_std());
                    assert_eq_api!(mv, v => v.get_unchecked_mut(..i.into_tic()).into_std());

                    if i < v.len() {
                        assert_eq_api!(cv, v => v[..=i.into_tic()].into_std());
                        assert_eq_api!(cv, v => v.get_unchecked(..=i.into_tic()).into_std());
                        assert_eq_api!(mv, v => v.get_unchecked_mut(..=i.into_tic()).into_std());
                    }

                    let r = (Bound::Included(i), Bound::Unbounded);
                    assert_eq_api!(cv, v => v.get_unchecked(r.into_tic()).into_std());
                    assert_eq_api!(mv, v => v.get_unchecked_mut(r.into_tic()).into_std());

                    let r = (Bound::Unbounded, Bound::Excluded(i));
                    assert_eq_api!(cv, v => v.get_unchecked(r.into_tic()).into_std());
                    assert_eq_api!(mv, v => v.get_unchecked_mut(r.into_tic()).into_std());

                    if i < v.len() {
                        let r = (Bound::Excluded(i), Bound::Unbounded);
                        assert_eq_api!(cv, v => v.get_unchecked(r.into_tic()).into_std());
                        assert_eq_api!(mv, v => v.get_unchecked_mut(r.into_tic()).into_std());

                        let r = (Bound::Unbounded, Bound::Included(i));
                        assert_eq_api!(cv, v => v.get_unchecked(r.into_tic()).into_std());
                        assert_eq_api!(mv, v => v.get_unchecked_mut(r.into_tic()).into_std());
                    }
                }
            }

            for a in 0..5usize {
                for b in 0..5usize {
                    assert_eq_api!(cv, v => v.get((a..b).into_tic()).into_std());
                    assert_eq_api!(mv, v => v.get_mut((a..b).into_tic()).into_std());

                    assert_eq_api!(cv, v => v.get((a..=b).into_tic()).into_std());
                    assert_eq_api!(mv, v => v.get_mut((a..=b).into_tic()).into_std());

                    let r = (Bound::Included(a), Bound::Excluded(b));
                    assert_eq_api!(cv, v => v.get(r.into_tic()).into_std());
                    assert_eq_api!(mv, v => v.get_mut(r.into_tic()).into_std());

                    let r = (Bound::Included(a), Bound::Included(b));
                    assert_eq_api!(cv, v => v.get(r.into_tic()).into_std());
                    assert_eq_api!(mv, v => v.get_mut(r.into_tic()).into_std());

                    let r = (Bound::Excluded(a), Bound::Excluded(b));
                    assert_eq_api!(cv, v => v.get(r.into_tic()).into_std());
                    assert_eq_api!(mv, v => v.get_mut(r.into_tic()).into_std());

                    let r = (Bound::Excluded(a), Bound::Included(b));
                    assert_eq_api!(cv, v => v.get(r.into_tic()).into_std());
                    assert_eq_api!(mv, v => v.get_mut(r.into_tic()).into_std());
                }
            }

            for a in 0..=v.len() {
                for b in a..=v.len() {
                    unsafe {
                        assert_eq_api!(cv, v => v[(a..b).into_tic()].into_std());
                        assert_eq_api!(cv, v => v.get_unchecked((a..b).into_tic()).into_std());
                        assert_eq_api!(mv, v => v.get_unchecked_mut((a..b).into_tic()).into_std());

                        if a < v.len() && b < v.len() {
                            assert_eq_api!(cv, v => v[(a..=b).into_tic()].into_std());
                            assert_eq_api!(cv, v => v.get_unchecked((a..=b).into_tic()).into_std());
                            assert_eq_api!(mv, v => v.get_unchecked_mut((a..=b).into_tic()).into_std());
                        }

                        let r = (Bound::Included(a), Bound::Excluded(b));
                        assert_eq_api!(cv, v => v.get_unchecked(r.into_tic()).into_std());
                        assert_eq_api!(mv, v => v.get_unchecked_mut(r.into_tic()).into_std());

                        if a < v.len() && b < v.len() {
                            let r = (Bound::Included(a), Bound::Included(b));
                            assert_eq_api!(cv, v => v.get_unchecked(r.into_tic()).into_std());
                            assert_eq_api!(mv, v => v.get_unchecked_mut(r.into_tic()).into_std());
                        }

                        if a < b {
                            let r = (Bound::Excluded(a), Bound::Excluded(b));
                            assert_eq_api!(cv, v => v.get_unchecked(r.into_tic()).into_std());
                            assert_eq_api!(mv, v => v.get_unchecked_mut(r.into_tic()).into_std());
                        }

                        if a < v.len() && b < v.len() {
                            let r = (Bound::Excluded(a), Bound::Included(b));
                            assert_eq_api!(cv, v => v.get_unchecked(r.into_tic()).into_std());
                            assert_eq_api!(mv, v => v.get_unchecked_mut(r.into_tic()).into_std());
                        }
                    }
                }
            }

            assert_eq_api!(cv, v => v.iter().collect_to_vec());
            assert_eq_api!(cv, v => v.into_iter().collect_to_vec());

            assert_eq_api!(mv, v => v.iter().collect_to_vec());
            assert_eq_api!(mv, v => v.iter_mut().collect_to_vec());
            assert_eq_api!(mv, v => v.into_iter().collect_to_vec());

            for l in 1..5 {
                assert_eq_api!(cv, v => v.windows(l).map_into_std().collect_to_vec());
                assert_eq_api!(cv, v => v.chunks(l).map_into_std().collect_to_vec());
                assert_eq_api!(mv, v => v.chunks_mut(l).map_into_std().collect_to_vec());
                assert_eq_api!(cv, v => v.chunks_exact(l).map_into_std().collect_to_vec());
                assert_eq_api!(mv, v => v.chunks_exact_mut(l).map_into_std().collect_to_vec());
                assert_eq_api!(cv, v => v.rchunks(l).map_into_std().collect_to_vec());
                assert_eq_api!(mv, v => v.rchunks_mut(l).map_into_std().collect_to_vec());
                assert_eq_api!(cv, v => v.rchunks(l).map_into_std().collect_to_vec());
                assert_eq_api!(mv, v => v.rchunks_mut(l).map_into_std().collect_to_vec());
                assert_eq_api!(cv, v => v.rchunks(l).map_into_std().collect_to_vec());
                assert_eq_api!(mv, v => v.rchunks_mut(l).map_into_std().collect_to_vec());
                assert_eq_api!(cv, v => v.rchunks_exact(l).map_into_std().collect_to_vec());
                assert_eq_api!(mv, v => v.rchunks_exact_mut(l).map_into_std().collect_to_vec());

                assert_eq_api!(
                    cv, v => v.chunk_by(|a, b| a.abs_diff(*b) < 2)
                        .map_into_std().collect_to_vec()
                );
                assert_eq_api!(
                    mv, v => v.chunk_by_mut(|a, b| a.abs_diff(*b) < 2)
                        .map_into_std().collect_to_vec()
                );
            }

            for i in 0..5 {
                assert_eq_api!(cv, v => v.split_at_checked(i.into_tic()).into_std());
                assert_eq_api!(mv, v => v.split_at_mut_checked(i.into_tic()).into_std());
            }

            for i in 0..v.len() {
                assert_eq_api!(cv, v => v.split_at(i.into_tic()).into_std());
                assert_eq_api!(mv, v => v.split_at_mut(i.into_tic()).into_std());
                unsafe {
                    assert_eq_api!(cv, v => v.split_at_unchecked(i.into_tic()).into_std());
                    assert_eq_api!(mv, v => v.split_at_mut_unchecked(i.into_tic()).into_std());
                }
            }

            for d in 1..5 {
                assert_eq_api!(
                    cv, v => v.split(|v| v % d == 0)
                        .map_into_std().collect_to_vec()
                );
                assert_eq_api!(
                    mv, v => v.split_mut(|v| v % d == 0)
                        .map_into_std().collect_to_vec()
                );
                assert_eq_api!(
                    cv, v => v.rsplit(|v| v % d == 0)
                        .map_into_std().collect_to_vec()
                );
                assert_eq_api!(
                    mv, v => v.rsplit_mut(|v| v % d == 0)
                        .map_into_std().collect_to_vec()
                );
                assert_eq_api!(
                    cv, v => v.split_inclusive(|v| v % d == 0)
                        .map_into_std().collect_to_vec()
                );
                assert_eq_api!(
                    mv, v => v.split_inclusive_mut(|v| v % d == 0)
                        .map_into_std().collect_to_vec()
                );
                for n in 0..5 {
                    assert_eq_api!(
                        cv, v => v.splitn(n, |v| v % d == 0)
                            .map_into_std().collect_to_vec()
                    );
                    assert_eq_api!(
                        mv, v => v.splitn_mut(n, |v| v % d == 0)
                            .map_into_std().collect_to_vec()
                    );
                    assert_eq_api!(
                        cv, v => v.rsplitn(n, |v| v % d == 0)
                            .map_into_std().collect_to_vec()
                    );
                    assert_eq_api!(
                        mv, v => v.rsplitn_mut(n, |v| v % d == 0)
                            .map_into_std().collect_to_vec()
                    );
                }
            }

            for a in 1..5 {
                assert_eq_api!(cv, v => v.contains(&a));
                assert_eq_api!(cv, v => v.binary_search(&a).into_std());
                assert_eq_api!(cv, v => v.binary_search_by(|b| b.cmp(&a).reverse()).into_std());
                assert_eq_api!(
                    cv, v => v.binary_search_by_key(&a, |b| 10_u32.wrapping_sub(*b)).into_std()
                );
            }

            for a in &[&[][..], &[0], &[1, 2], &[3, 4], &[1, 3], &[3, 5]] {
                assert_eq_api!(cv, v => v.starts_with(a.into_tic()));
                assert_eq_api!(cv, v => v.ends_with(a.into_tic()));
            }

            for i in 0..v.len() {
                unsafe {
                    assert_eq_api!(cv, v => v[i.into_tic()..].align_to::<u64>().into_std());
                    let mv = &mut *mv.0;
                    let slices = mv.align_to_mut::<u64>();
                    let ptrs1 = (
                        slices.0.as_ptr_range(),
                        slices.1.as_ptr_range(),
                        slices.2.as_ptr_range(),
                    );
                    let slices = TiSlice::<Id, _>::from_mut(mv).align_to_mut::<u64>();
                    let ptrs2 = (
                        slices.0.as_ptr_range(),
                        slices.1.as_ptr_range(),
                        slices.2.as_ptr_range(),
                    );
                    assert_eq!(ptrs1, ptrs2);
                }
            }

            for a in 1..5 {
                assert_eq_api!(cv, v => v.partition_point(|b| *b < a).into_std());
            }
        }
    }

    #[test]
    fn test_slice_write_core_api_compatibility() {
        for v in [
            &[0_u32; 0][..],
            &[1],
            &[1, 1234],
            &[1, 2, 4],
            &[1, 5, 3, 2],
            &[1, 1, 9, 2, 4, 1, 12345, 12],
        ] {
            let mut mv = (v.to_vec(), v.to_vec());
            let mut mv = (mv.0.as_mut_slice(), TiSlice::from_mut(mv.1.as_mut_slice()));
            let restore = |mv: &mut (&mut [u32], &mut TiSlice<Id, u32>)| {
                mv.0.copy_from_slice(v);
                mv.1.raw.copy_from_slice(v);
            };

            restore(&mut mv);
            assert_eq_api!(mv, v => v.into_iter().for_each(|item| *item += 1));

            restore(&mut mv);
            for i in 0..v.len() {
                for j in 0..v.len() {
                    assert_eq_api!(mv, v => v.swap(i.into_tic(), j.into_tic()));
                }
            }

            restore(&mut mv);
            assert_eq_api!(mv, v => v.reverse());

            restore(&mut mv);
            assert_eq_api!(mv, v => v.sort_unstable());

            restore(&mut mv);
            assert_eq_api!(mv, v => v.sort_unstable_by(|a, b| b.cmp(a)));

            restore(&mut mv);
            assert_eq_api!(mv, v => v.sort_unstable_by_key(|a| a * (a % 3)));

            for i in 0..v.len() {
                restore(&mut mv);
                assert_eq_api!(mv, v => v.select_nth_unstable(i.into_tic()).into_std());
            }

            for i in 0..v.len() {
                restore(&mut mv);
                assert_eq_api!(mv, v => v.select_nth_unstable_by(
                    i.into_tic(), |a, b| b.cmp(a)
                ).into_std());
            }

            for i in 0..v.len() {
                restore(&mut mv);
                assert_eq_api!(mv, v => v.select_nth_unstable_by_key(
                    i.into_tic(), |a| a * (a % 3)
                ).into_std());
            }

            for a in 0..v.len() {
                restore(&mut mv);
                assert_eq_api!(mv, v => v.rotate_left(a.into_tic()));
                restore(&mut mv);
                assert_eq_api!(mv, v => v.rotate_right(a.into_tic()));
            }

            restore(&mut mv);
            assert_eq_api!(mv, v => v.fill(123));

            restore(&mut mv);
            assert_eq_api!(mv, v => { let mut a = 1; v.fill_with(|| { a *= 2; a }) });

            for a in 0..v.len() {
                for b in a..v.len() {
                    for c in 0..v.len() - (b - a) {
                        restore(&mut mv);
                        assert_eq_api!(mv, v => v.copy_within((a..b).into_tic(), c.into_tic()));
                    }
                }
            }

            restore(&mut mv);
            // let w: Vec<_> = v.into_iter().map(|v| v ^ 0b1010_1010).collect();
            let mut w = [0; 8];
            w[0..v.len()].copy_from_slice(v);
            for w in &mut w {
                *w ^= 0b1010_1010;
            }

            let mut mw = (w, w);
            let mut mw = (
                &mut mw.0[0..v.len()],
                TiSlice::from_mut(&mut mw.1[0..v.len()]),
            );
            mv.0.swap_with_slice(mw.0);
            mv.1.swap_with_slice(mw.1);
            assert_eq_api!(mv, v => (*v).into_std());
            assert_eq_api!(mw, w => (*w).into_std());
        }

        let vs = [&[0; 0][..], &[1], &[1, 2], &[1, 2, 4], &[1, 2, 3, 5]];
        for v in vs {
            let mut mv = (v.to_vec(), v.to_vec());
            let mut mv = (mv.0.as_mut_slice(), TiSlice::from_mut(mv.1.as_mut_slice()));

            for w in vs {
                let l = v.len().min(w.len());
                assert_eq_api!(
                    mv,
                    v => v[..l.into_tic()].copy_from_slice(w[..l].into_tic())
                );
            }
        }

        let vs = [
            &[NonCopy(0); 0][..],
            &[NonCopy(1)],
            &[NonCopy(1), NonCopy(2)],
            &[NonCopy(1), NonCopy(2), NonCopy(4)],
            &[NonCopy(1), NonCopy(2), NonCopy(3), NonCopy(5)],
        ];
        for v in vs {
            let mut mv = (v.to_vec(), v.to_vec());
            let mut mv = (mv.0.as_mut_slice(), TiSlice::from_mut(mv.1.as_mut_slice()));

            for w in vs {
                let l = v.len().min(w.len());
                assert_eq_api!(
                    mv,
                    v => v[..l.into_tic()].clone_from_slice(w[..l].into_tic())
                );
            }
        }
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_slice_hash_compatibility() {
        for v in [
            &[0_u32; 0][..],
            &[1],
            &[1, 1234],
            &[1, 2, 4],
            &[1, 5, 3, 2],
            &[1, 1, 9, 2, 4, 1, 12345, 12],
        ] {
            let mut cv = (v, TiSlice::<Id, _>::from_ref(v));
            assert_eq_api!(cv, v => {
                let mut hasher = DefaultHasher::new();
                v.hash(&mut hasher);
                hasher.finish()
            });
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_slice_read_alloc_api_compatibility() {
        for v in [
            &[0_u32; 0][..],
            &[1],
            &[1, 1234],
            &[1, 2, 4],
            &[1, 5, 3, 2],
            &[1, 1, 9, 2, 4, 1, 12345, 12],
        ] {
            let mut cv = (v, TiSlice::from_ref(v));

            assert_eq_api!(cv, v => Cow::from(v).into_std());
            assert_eq_api!(cv, v => matches!(Cow::from(v), Cow::Borrowed(_)));
            assert_eq_api!(cv, v => Cow::from(v).into_owned().into_std());
            assert_eq_api!(cv, v => v.to_vec().into_std());
            assert_eq_api!(cv, v => v.to_vec().into_boxed_slice().into_std());
            assert_eq_api!(cv, v => v.to_vec().into_boxed_slice().into_vec().into_std());
            assert_eq_api!(cv, v => v.to_owned().into_std());
            assert_eq_api!(cv, v => v.repeat(5).into_std());
        }

        for v in [
            &[&[1, 2][..], &[3, 4]][..],
            &[&[1, 2], &[]],
            &[&[], &[3, 4]],
        ] {
            let mut cv = (v, TiSlice::from_ref(v));

            assert_eq_api!(cv, v => v.concat().into_std());
            assert_eq_api!(cv, v => v.join(&0).into_std());
            assert_eq_api!(cv, v => v.join(&[1, 2, 3][..]).into_std());
        }
    }

    #[cfg(feature = "alloc")]
    #[expect(clippy::stable_sort_primitive, reason = "okay in tests")]
    #[test]
    fn test_slice_write_alloc_api_compatibility() {
        for v in [
            &[0_u32; 0][..],
            &[1],
            &[1, 1234],
            &[1, 2, 4],
            &[1, 5, 3, 2],
            &[1, 1, 9, 2, 4, 1, 12345, 12],
        ] {
            let mut mv = (v.to_vec(), v.to_vec());
            let mut mv = (mv.0.as_mut_slice(), TiSlice::from_mut(mv.1.as_mut_slice()));

            let re = |mv: &mut (&mut [u32], &mut TiSlice<Id, u32>)| {
                mv.0.copy_from_slice(v);
                mv.1.raw.copy_from_slice(v);
            };

            re(&mut mv);
            assert_eq_api!(mv, v => v.sort());
            re(&mut mv);
            assert_eq_api!(mv, v => v.sort_by(|a, b| b.cmp(a)));
            re(&mut mv);
            assert_eq_api!(mv, v => v.sort_by_key(|a| a * (a % 3)));
            re(&mut mv);
            assert_eq_api!(mv, v => v.sort_by_cached_key(|a| a * (a % 3)));
        }
    }

    #[test]
    fn test_u8_slice_read_core_api_compatibility() {
        for v in [&b"abc"[..], b"aBc", b"ABC", b"abd", b"a\x80\x81b"] {
            let mut cv = (v, TiSlice::from_ref(v));
            assert_eq_api!(cv, v => v.is_ascii());
            assert_eq_api!(cv, v => v.trim_ascii_start().into_std());
            assert_eq_api!(cv, v => v.trim_ascii_end().into_std());
            assert_eq_api!(cv, v => v.trim_ascii().into_std());
            assert_eq_api!(cv, v => v.eq_ignore_ascii_case(b"aBc".into_tic()));
            assert_eq_api!(cv, v => v.escape_ascii().collect_to_vec());
            assert_eq_api!(cv, v => v.utf8_chunks().collect_to_vec());
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_str_slice_read_alloc_api_compatibility() {
        let v = &["abc", "aBc", "ABC", "abd"][..];
        let mut cv = (v, TiSlice::<Id, _>::from_ref(v));
        assert_eq_api!(cv, v => v.concat());
        assert_eq_api!(cv, v => v.join("foo"));
    }

    #[test]
    fn test_u8_slice_write_core_api_compatibility() {
        for v in [&b"abc"[..], b"aBc", b"ABC", b"abd", b"\x80\x81"] {
            let mut mv = (v.to_vec(), v.to_vec());
            let mut mv = (mv.0.as_mut_slice(), TiSlice::from_mut(mv.1.as_mut_slice()));
            assert_eq_api!(mv, v => v.make_ascii_uppercase());
            assert_eq_api!(mv, v => (*v).into_std());
            assert_eq_api!(mv, v => v.make_ascii_lowercase());
            assert_eq_api!(mv, v => (*v).into_std());
        }
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_u8_slice_read_alloc_api_compatibility() {
        for v in [&b"abc"[..], b"aBc", b"ABC", b"abd", b"\x80\x81"] {
            let mut cv = (v, TiSlice::from_ref(v));
            assert_eq_api!(cv, v => v.to_ascii_uppercase().into_std());
            assert_eq_api!(cv, v => v.to_ascii_lowercase().into_std());
        }
    }

    #[test]
    fn test_slice_non_zero_indexes() {
        use core::mem::size_of;
        use core::num::NonZeroUsize;

        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        struct Id(NonZeroUsize);

        impl From<usize> for Id {
            fn from(value: usize) -> Self {
                Self(NonZeroUsize::new(value + 1).unwrap())
            }
        }

        assert_eq!(size_of::<Option<Id>>(), size_of::<Id>());

        let slice: &TiSlice<Id, usize> = TiSlice::from_ref(&[1, 2, 4, 8, 16]);
        assert_eq!(
            slice.first_key_value(),
            Some((Id(NonZeroUsize::new(1).unwrap()), &1))
        );
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_slice_read() {
        let arr = core::array::from_fn::<_, 128, _>(|i| {
            let i = u8::try_from(i).unwrap();
            i % 2 + i % 3 + i % 5 + i % 7 + i % 11 + i % 13 + i % 17 + i % 19
        });
        for v in [
            &[0_u8; 0][..],
            &[1],
            &[1, 123],
            &[1, 2, 4, 3, 9, 27, 4, 16, 255],
            &[123; 31],
            b"abc",
            &arr,
        ] {
            let ov = (v, TiSlice::<Id, _>::from_ref(v));

            for n in [0, 1, 2, 3, 4, 16, 256] {
                let mut cv = ov;
                assert_eq_api!(cv, v => {
                    let mut buf = [0; 256];
                    let slice = &mut buf[0..n];
                    (v.read(slice).unwrap(), slice.len(), buf)
                });
            }

            for n in [0, 1, 2, 3, 4, 16, 256] {
                for m in [0, 1, 2, 3, 4, 16, 256] {
                    let mut cv = ov;
                    assert_eq_api!(cv, v => {
                        let mut buf1 = [0; 256];
                        let mut buf2 = [0; 256];
                        let ios1 = IoSliceMut::new(&mut buf1[0..n]);
                        let ios2 = IoSliceMut::new(&mut buf2[0..m]);
                        let ios3 = &mut [ios1, ios2];
                        (
                            v.read_vectored(ios3).unwrap(),
                            ios3.len(),
                            ios3[0].len(),
                            ios3[1].len(),
                            buf1,
                            buf2,
                        )
                    });
                }
            }

            for n in [0, 1, 2, 3, 4, 16, 256] {
                let mut cv = ov;
                assert_eq_api!(cv, v => {
                    let mut buf = [0; 256];
                    let slice = &mut buf[0..n];
                    match v.read_exact(slice) {
                        Ok(len) => Ok((len, slice.len(), buf)),
                        Err(err) => Err(err.to_string()),
                    }
                });
            }

            let mut cv = ov;
            assert_eq_api!(cv, v => {
                let mut buf = Vec::new();
                (v.read_to_end(&mut buf).unwrap(), buf)
            });

            let mut cv = ov;
            assert_eq_api!(cv, v => {
                let mut buf = String::new();
                match v.read_to_string(&mut buf) {
                    Ok(len) => Ok((len, buf)),
                    Err(err) => Err(err.to_string()),
                }
            });
        }
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_slice_buf_read() {
        let arr = core::array::from_fn::<_, 128, _>(|i| {
            let i = u8::try_from(i).unwrap();
            i % 2 + i % 3 + i % 5 + i % 7 + i % 11 + i % 13 + i % 17 + i % 19
        });
        for v in [
            &[0_u8; 0][..],
            &[1],
            &[1, 123],
            &[1, 2, 4, 3, 9, 27, 4, 16, 255],
            &[123; 31],
            &arr,
        ] {
            let ov = (v, TiSlice::<Id, _>::from_ref(v));

            let mut cv = ov;
            assert_eq_api!(cv, v => v.fill_buf().unwrap());

            for n in [0, 1, 2, 3, 4, 16, 256] {
                if n <= v.len() {
                    let mut cv = ov;
                    assert_eq_api!(cv, v => {
                        v.consume(n);
                        v.fill_buf().unwrap()
                    });
                }
            }
        }
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_slice_write() {
        let ov = (&mut [0; 16][..], &mut [0; 16]);
        let ov = (ov.0, TiSlice::<Id, u8>::from_mut(ov.1));
        let mut mv = (&mut *ov.0, &mut *ov.1);
        let mut mv = (&mut mv.0, &mut mv.1);

        assert_eq_api!(mv, v => v.write(&[1, 2, 3]).unwrap());
        assert_eq_api!(mv, v => v.write(&[]).unwrap());
        assert_eq_api!(mv, v => v.write(&[2, 3]).unwrap());
        assert_eq_api!(mv, v => v.write_vectored(
            &[IoSlice::new(&[3, 4, 5]), IoSlice::new(&[]), IoSlice::new(&[5, 6])]
        ).unwrap());
        assert_eq_api!(mv, v => v.write_all(&[7, 8, 9]).unwrap());
        assert_eq_api!(mv, v => v.flush().unwrap());

        assert_eq!(*mv.0, &[0, 0, 0]);
        assert_eq!(&mv.1.raw, &[0, 0, 0]);
        assert_eq!(&ov.0, &[1, 2, 3, 2, 3, 3, 4, 5, 5, 6, 7, 8, 9, 0, 0, 0]);
        assert_eq!(&ov.1.raw, &[1, 2, 3, 2, 3, 3, 4, 5, 5, 6, 7, 8, 9, 0, 0, 0]);

        let ov = (&mut [0; 4][..], &mut [0; 4]);
        let ov = (ov.0, TiSlice::<Id, u8>::from_mut(ov.1));
        let mut mv = (&mut *ov.0, &mut *ov.1);
        let mut mv = (&mut mv.0, &mut mv.1);

        assert_eq_api!(mv, v => v.write_all(&[2, 3, 4, 5, 6, 7]).map_err(|err| err.to_string()));

        assert_eq!(*mv.0, &[0_u8; 0][..]);
        assert_eq!(&mv.1.raw, &[0_u8; 0][..]);
        assert_eq!(&ov.0, &[2, 3, 4, 5]);
        assert_eq!(&ov.1.raw, &[2, 3, 4, 5]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_slice_debug() {
        let s0: &TiSlice<Id, u32> = TiSlice::from_ref(&[]);
        let s1: &TiSlice<Id, u32> = TiSlice::from_ref(&[12]);
        let s2: &TiSlice<Id, u32> = TiSlice::from_ref(&[23, 34]);
        assert_eq!(&alloc::format!("{s0:?}"), "{}");
        assert_eq!(&alloc::format!("{s1:?}"), "{Id(0): 12}");
        assert_eq!(&alloc::format!("{s2:?}"), "{Id(0): 23, Id(1): 34}");
    }

    #[cfg(all(feature = "alloc", feature = "serde"))]
    #[test]
    fn test_slice_serialize() {
        let s0: &TiSlice<Id, u32> = TiSlice::from_ref(&[]);
        let s1: &TiSlice<Id, u32> = TiSlice::from_ref(&[12]);
        let s2: &TiSlice<Id, u32> = TiSlice::from_ref(&[23, 34]);
        assert_eq!(&serde_json::to_string(&s0).unwrap(), "[]");
        assert_eq!(&serde_json::to_string(&s1).unwrap(), "[12]");
        assert_eq!(&serde_json::to_string(&s2).unwrap(), "[23,34]");
    }

    #[should_panic(expected = "where expr: v.bad_return()")]
    #[test]
    fn test_api_compatibility_return_check_failure() {
        pub trait BadReturn {
            fn bad_return(&self) -> u32;
        }

        impl<T> BadReturn for [T] {
            fn bad_return(&self) -> u32 {
                12
            }
        }

        impl<K, V> BadReturn for TiSlice<K, V> {
            fn bad_return(&self) -> u32 {
                23
            }
        }

        let v = &[1, 2, 3][..];
        let mut cv = (v, TiSlice::<Id, _>::from_ref(v));
        assert_eq_api!(cv, v => v.bad_return());
    }

    #[should_panic(expected = "where expr: v.bad_modify()")]
    #[test]
    fn test_api_compatibility_modify_check_failure() {
        pub trait BadModify {
            fn bad_modify(&mut self);
        }

        impl<T> BadModify for [T] {
            fn bad_modify(&mut self) {}
        }

        impl<K, V> BadModify for TiSlice<K, V> {
            fn bad_modify(&mut self) {
                self.reverse();
            }
        }

        let v = (&mut [1, 2, 3][..], &mut [1, 2, 3][..]);
        let mut mv = (v.0, TiSlice::<Id, _>::from_mut(v.1));
        assert_eq_api!(mv, v => v.bad_modify());
    }
}
