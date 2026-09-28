use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::collections::TryReserveError;
use alloc::ffi::CString;
use alloc::string::String;
use alloc::vec::{self, Drain, Splice, Vec};
use core::borrow::{Borrow, BorrowMut};
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::iter::FromIterator;
use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ops::{Deref, DerefMut, Index, IndexMut};
use core::{fmt, slice};
#[cfg(feature = "std")]
use std::io::{IoSlice, Result as IoResult, Write};

#[cfg(feature = "bincode")]
use bincode::de::{BorrowDecode, BorrowDecoder, Decode, Decoder};
#[cfg(feature = "bincode")]
use bincode::enc::{Encode, Encoder};
#[cfg(feature = "bincode")]
use bincode::error::{DecodeError, EncodeError};
#[cfg(all(feature = "alloc", feature = "serde"))]
use serde::de::{Deserialize, Deserializer};
#[cfg(feature = "serde")]
use serde::ser::{Serialize, Serializer};

use crate::alloc_ext::{Allocator, Global};
use crate::{TiEnumerated, TiRangeBounds, TiSlice, TiSliceIndex};

/// A contiguous growable array type
/// that only accepts keys of the type `K`.
///
/// `TiVec<K, V>` is a wrapper around Rust container type [`std::vec::Vec`].
/// The struct mirrors the stable API of Rust [`std::vec::Vec`]
/// and forwards to it as much as possible.
///
/// `TiVec<K, V>` uses `K` instead of `usize` for element indices and
/// require the index to implement
/// [`From<usize>`][`From`] and [`Into<usize>`][`Into`] traits.
/// Their implementation can be easily done
/// with [`derive_more`] crate and `#[derive(From, Into)]`.
///
/// `TiVec<K, V>` can be converted to [`std::vec::Vec<V>`][`std::vec::Vec`] and
/// back using [`From`] and [`Into`].
///
/// There are also zero-cost conversions available between references:
/// - [`&std::vec::Vec<V>`][`std::vec::Vec`] and `&TiVec<K, V>` with [`AsRef`],
/// - [`&mut std::vec::Vec<V>`][`std::vec::Vec`] and `&mut TiVec<K, V>` with
///   [`AsMut`],
///
/// Added methods:
/// - [`from_ref`] - Converts a [`&std::vec::Vec<V>`][`std::vec::Vec`] into a
///   `&TiVec<K, V>`.
/// - [`from_mut`] - Converts a [`&mut std::vec::Vec<V>`][`std::vec::Vec`] into
///   a `&mut TiVec<K, V>`.
/// - [`push_and_get_key`] - Appends an element to the back of a collection and
///   returns its index of type `K`.
/// - [`pop_key_value`] - Removes the last element from a vector and returns it
///   with its index of type `K`, or [`None`] if the vector is empty.
/// - [`pop_key_value_if`] - Removes the last element from a vector and returns
///   it with its index of type `K`, or [`None`] if the predicate returns false
///   or the vector is empty.
/// - [`drain_enumerated`] - Creates a draining iterator that removes the
///   specified range in the vector and yields the current count and the removed
///   items. It acts like `self.drain(range).enumerate()`, but instead of
///   `usize` it returns index of type `K`.
/// - [`into_iter_enumerated`] - Converts the vector into iterator over all
///   key-value pairs with `K` used for iteration indices. It acts like
///   `self.into_iter().enumerate()`, but use `K` instead of `usize` for
///   iteration indices.
///
/// # Example
///
/// ```
/// use derive_more::{From, Into};
/// use typed_index_collections::TiVec;
///
/// #[derive(From, Into)]
/// struct FooId(usize);
///
/// let mut foos: TiVec<FooId, usize> = std::vec![10, 11, 13].into();
/// foos.insert(FooId(2), 12);
/// assert_eq!(foos[FooId(2)], 12);
/// ```
///
/// [`from_ref`]: #method.from_ref
/// [`from_mut`]: #method.from_mut
/// [`push_and_get_key`]: #method.push_and_get_key
/// [`pop_key_value`]: #method.pop_key_value
/// [`pop_key_value_if`]: #method.pop_key_value_if
/// [`drain_enumerated`]: #method.drain_enumerated
/// [`into_iter_enumerated`]: #method.into_iter_enumerated
/// [`std::vec::Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
/// [`From`]: https://doc.rust-lang.org/std/convert/trait.From.html
/// [`Into`]: https://doc.rust-lang.org/std/convert/trait.Into.html
/// [`AsRef`]: https://doc.rust-lang.org/std/convert/trait.AsRef.html
/// [`AsMut`]: https://doc.rust-lang.org/std/convert/trait.AsMut.html
/// [`derive_more`]: https://crates.io/crates/derive_more
#[repr(transparent)]
pub struct TiVec<K, V, A: Allocator = Global> {
    /// Raw slice property
    #[cfg(feature = "nightly")]
    pub raw: Vec<V, A>,

    /// Raw slice property
    #[cfg(not(feature = "nightly"))]
    pub raw: Vec<V>,

    // Dummy allocator
    #[cfg(not(feature = "nightly"))]
    _alloc: PhantomData<A>,

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
}

impl<K, V> TiVec<K, V, Global> {
    /// Constructs a new, empty `TiVec<K, V>`.
    ///
    /// See [`Vec::new`] for more details.
    ///
    /// [`Vec::new`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.new
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            raw: Vec::new(),
            #[cfg(not(feature = "nightly"))]
            _alloc: PhantomData,
            _marker: PhantomData,
        }
    }

    /// Constructs a new, empty `TiVec<K, V>` with the specified capacity.
    ///
    /// See [`Vec::with_capacity`] for more details.
    ///
    /// [`Vec::with_capacity`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.with_capacity
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            raw: Vec::with_capacity(capacity),
            #[cfg(not(feature = "nightly"))]
            _alloc: PhantomData,
            _marker: PhantomData,
        }
    }

    /// Creates a `TiVec<K, V>` directly from the raw components of another
    /// vector.
    ///
    /// See [`Vec::from_raw_parts`] for more details.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked.
    /// See [`Vec::from_raw_parts`] for more details.
    ///
    /// [`Vec::from_raw_parts`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.from_raw_parts
    #[inline]
    pub unsafe fn from_raw_parts(ptr: *mut V, length: usize, capacity: usize) -> Self {
        Self {
            // SAFETY: Guaranteed by the caller.
            raw: unsafe { Vec::from_raw_parts(ptr, length, capacity) },
            #[cfg(not(feature = "nightly"))]
            _alloc: PhantomData,
            _marker: PhantomData,
        }
    }
}

impl<K, V, A: Allocator> TiVec<K, V, A> {
    /// Constructs a new, empty `TiVec<K, V>`.
    ///
    /// See [`Vec::new`] for more details.
    ///
    /// [`Vec::new`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.new
    #[inline]
    #[must_use]
    pub fn new_in(alloc: A) -> Self {
        #[cfg(not(feature = "nightly"))]
        drop(alloc);

        Self {
            #[cfg(feature = "nightly")]
            raw: Vec::new_in(alloc),
            #[cfg(not(feature = "nightly"))]
            raw: Vec::new(),
            #[cfg(not(feature = "nightly"))]
            _alloc: PhantomData,
            _marker: PhantomData,
        }
    }

    /// Constructs a new, empty `TiVec<K, V>` with the specified capacity.
    ///
    /// See [`Vec::with_capacity`] for more details.
    ///
    /// [`Vec::with_capacity`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.with_capacity
    #[inline]
    #[must_use]
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        #[cfg(not(feature = "nightly"))]
        drop(alloc);

        Self {
            #[cfg(feature = "nightly")]
            raw: Vec::with_capacity_in(capacity, alloc),
            #[cfg(not(feature = "nightly"))]
            raw: Vec::with_capacity(capacity),
            #[cfg(not(feature = "nightly"))]
            _alloc: PhantomData,
            _marker: PhantomData,
        }
    }

    /// Creates a `TiVec<K, V>` directly from the raw components of another
    /// vector.
    ///
    /// See [`Vec::from_raw_parts`] for more details.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked.
    /// See [`Vec::from_raw_parts`] for more details.
    ///
    /// [`Vec::from_raw_parts`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.from_raw_parts
    #[inline]
    pub unsafe fn from_raw_parts_in(ptr: *mut V, length: usize, capacity: usize, alloc: A) -> Self {
        #[cfg(not(feature = "nightly"))]
        drop(alloc);

        Self {
            #[cfg(feature = "nightly")]
            // SAFETY: Guaranteed by the caller.
            raw: unsafe { Vec::from_raw_parts_in(ptr, length, capacity, alloc) },

            #[cfg(not(feature = "nightly"))]
            // SAFETY: Guaranteed by the caller.
            raw: unsafe { Vec::from_raw_parts(ptr, length, capacity) },

            #[cfg(not(feature = "nightly"))]
            _alloc: PhantomData,

            _marker: PhantomData,
        }
    }

    /// Decomposes a `TiVec<K, V>` into its raw components.
    ///
    /// See [`Vec::into_raw_parts`] for more details.
    #[inline]
    #[must_use]
    pub fn into_raw_parts(self) -> (*mut V, usize, usize) {
        let mut me = ManuallyDrop::new(self);
        (me.as_mut_ptr(), me.len(), me.capacity())
    }

    /// Decomposes a `TiVec<K, V>` into its raw components.
    ///
    /// See [`Vec::into_raw_parts_with_allocator`] for more details.
    #[cfg(feature = "nightly")]
    #[inline]
    #[must_use]
    pub fn into_raw_parts_with_allocator(self) -> (*mut V, usize, usize, A) {
        let mut me = ManuallyDrop::new(self);
        let len = me.len();
        let capacity = me.capacity();
        let ptr = me.as_mut_ptr();
        // SAFETY: `me` is a `ManuallyDrop`, so it will not be dropped.
        // We are moving the allocator out of it and returning it, so the caller
        // becomes responsible for it.
        // The original allocator inside `me` is not dropped.
        let alloc = unsafe { core::ptr::read(me.allocator()) };
        (ptr, len, capacity, alloc)
    }

    /// Converts a [`&std::vec::Vec<V>`] into a `&TiVec<K, V>`.
    ///
    /// Vector reference is intentionally used in the argument
    /// instead of slice reference for conversion with no-op.
    ///
    /// # Example
    ///
    /// ```
    /// # use typed_index_collections::TiVec;
    /// pub struct Id(usize);
    /// let vec: &TiVec<Id, usize> = TiVec::from_ref(&vec![1, 2, 4]);
    /// ```
    ///
    /// [`&std::vec::Vec<V>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    #[cfg(feature = "nightly")]
    #[inline]
    #[must_use]
    pub const fn from_ref(raw: &Vec<V, A>) -> &Self {
        // SAFETY: `TiVec<K, V>` is `repr(transparent)` over a `Vec<V>` type.
        unsafe { &*core::ptr::from_ref::<Vec<V, A>>(raw).cast::<Self>() }
    }

    /// Converts a [`&std::vec::Vec<V>`] into a `&TiVec<K, V>`.
    ///
    /// Vector reference is intentionally used in the argument
    /// instead of slice reference for conversion with no-op.
    ///
    /// # Example
    ///
    /// ```
    /// # use typed_index_collections::TiVec;
    /// pub struct Id(usize);
    /// let vec: &TiVec<Id, usize> = TiVec::from_ref(&vec![1, 2, 4]);
    /// ```
    ///
    /// [`&std::vec::Vec<V>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    #[cfg(not(feature = "nightly"))]
    #[inline]
    #[must_use]
    pub const fn from_ref(raw: &Vec<V>) -> &Self {
        // SAFETY: `TiVec<K, V>` is `repr(transparent)` over a `Vec<V>` type.
        unsafe { &*core::ptr::from_ref::<Vec<V>>(raw).cast::<Self>() }
    }

    /// Converts a [`&mut std::vec::Vec<V>`] into a `&mut TiVec<K, V>`.
    ///
    /// # Example
    ///
    /// ```
    /// # use typed_index_collections::TiVec;
    /// pub struct Id(usize);
    /// let vec: &mut TiVec<Id, usize> = TiVec::from_mut(&mut vec![1, 2, 4]);
    /// ```
    ///
    /// [`&mut std::vec::Vec<V>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn from_mut(raw: &mut Vec<V, A>) -> &mut Self {
        // SAFETY: `TiVec<K, V>` is `repr(transparent)` over a `Vec<V>` type.
        unsafe { &mut *core::ptr::from_mut::<Vec<V, A>>(raw).cast::<Self>() }
    }

    /// Converts a [`&mut std::vec::Vec<V>`] into a `&mut TiVec<K, V>`.
    ///
    /// # Example
    ///
    /// ```
    /// # use typed_index_collections::TiVec;
    /// pub struct Id(usize);
    /// let vec: &mut TiVec<Id, usize> = TiVec::from_mut(&mut vec![1, 2, 4]);
    /// ```
    ///
    /// [`&mut std::vec::Vec<V>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub const fn from_mut(raw: &mut Vec<V>) -> &mut Self {
        // SAFETY: `TiVec<K, V>` is `repr(transparent)` over a `Vec<V>` type.
        unsafe { &mut *core::ptr::from_mut::<Vec<V>>(raw).cast::<Self>() }
    }

    /// Returns the number of elements the vector can hold without
    /// reallocating.
    ///
    /// See [`Vec::capacity`] for more details.
    ///
    /// [`Vec::capacity`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.capacity
    #[inline]
    #[must_use]
    pub const fn capacity(&self) -> usize {
        self.raw.capacity()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `TiVec<K, V>`. The collection may reserve more space to
    /// avoid frequent reallocations. After calling `reserve`, capacity will
    /// be greater than or equal to `self.len() + additional`. Does nothing
    /// if capacity is already sufficient.
    ///
    /// See [`Vec::reserve`] for more details.
    ///
    /// [`Vec::reserve`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.reserve
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.raw.reserve(additional);
    }

    /// Reserves the minimum capacity for exactly `additional` more elements to
    /// be inserted in the given `TiVec<K, V>`. After calling `reserve_exact`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// See [`Vec::reserve_exact`] for more details.
    ///
    /// [`Vec::reserve_exact`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.reserve_exact
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.raw.reserve_exact(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be
    /// inserted in the given `Vec<T>`.
    ///
    /// See [`Vec::try_reserve`] for more details.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an
    /// error is returned.
    ///
    /// [`Vec::try_reserve`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.try_reserve
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.raw.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional`
    /// elements to be inserted in the given `Vec<T>`.
    ///
    /// See [`Vec::try_reserve_exact`] for more details.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an
    /// error is returned.
    ///
    /// [`Vec::try_reserve_exact`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.try_reserve_exact
    #[inline]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.raw.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// See [`Vec::shrink_to_fit`] for more details.
    ///
    /// [`Vec::shrink_to_fit`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.shrink_to_fit
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.raw.shrink_to_fit();
    }

    /// Shrinks the capacity of the vector with a lower bound.
    ///
    /// See [`Vec::shrink_to`] for more details.
    ///
    /// [`Vec::shrink_to`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.shrink_to
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.raw.shrink_to(min_capacity);
    }

    /// Converts the vector into [`Box<TiSlice<K, V>>`][`Box`].
    ///
    /// See [`Vec::into_boxed_slice`] for more details.
    ///
    /// [`Vec::into_boxed_slice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.into_boxed_slice
    /// [`Box`]: https://doc.rust-lang.org/std/boxed/struct.Box.html
    #[cfg(feature = "nightly")]
    #[inline]
    #[must_use]
    pub fn into_boxed_slice(self) -> Box<TiSlice<K, V>, A> {
        TiSlice::boxed_from(self.raw.into_boxed_slice())
    }

    /// Converts the vector into [`Box<TiSlice<K, V>>`][`Box`].
    ///
    /// See [`Vec::into_boxed_slice`] for more details.
    ///
    /// [`Vec::into_boxed_slice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.into_boxed_slice
    /// [`Box`]: https://doc.rust-lang.org/std/boxed/struct.Box.html
    #[cfg(not(feature = "nightly"))]
    #[inline]
    #[must_use]
    pub fn into_boxed_slice(self) -> Box<TiSlice<K, V>> {
        TiSlice::boxed_from(self.raw.into_boxed_slice())
    }

    /// Shortens the vector, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// See [`Vec::truncate`] for more details.
    ///
    /// [`Vec::truncate`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.truncate
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        self.raw.truncate(len);
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// See [`Vec::as_slice`] for more details.
    ///
    /// [`Vec::as_slice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_slice
    #[inline]
    #[must_use]
    pub const fn as_slice(&self) -> &TiSlice<K, V> {
        TiSlice::from_ref(self.raw.as_slice())
    }

    /// Extracts a mutable slice of the entire vector.
    ///
    /// See [`Vec::as_mut_slice`] for more details.
    ///
    /// [`Vec::as_mut_slice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_mut_slice
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut TiSlice<K, V> {
        TiSlice::from_mut(self.raw.as_mut_slice())
    }

    /// Returns a raw pointer to the vector's buffer.
    ///
    /// See [`Vec::as_ptr`] for more details.
    ///
    /// [`Vec::as_ptr`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_ptr
    #[inline]
    #[must_use]
    pub const fn as_ptr(&self) -> *const V {
        self.raw.as_ptr()
    }

    /// Returns an unsafe mutable pointer to the vector's buffer.
    ///
    /// See [`Vec::as_mut_ptr`] for more details.
    ///
    /// [`Vec::as_mut_ptr`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_mut_ptr
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut V {
        self.raw.as_mut_ptr()
    }

    /// Returns a reference to the underlying allocator.
    #[cfg(feature = "nightly")]
    #[inline]
    pub fn allocator(&self) -> &A {
        self.raw.allocator()
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// See [`Vec::set_len`] for more details.
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to [`capacity()`].
    /// - The elements at `old_len..new_len` must be initialized.
    ///
    /// [`Vec::set_len`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.set_len
    /// [`capacity()`]: #method.capacity
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        // SAFETY: Guaranteed by the caller.
        unsafe { self.raw.set_len(new_len) };
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// See [`Vec::swap_remove`] for more details.
    ///
    /// [`Vec::swap_remove`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.swap_remove
    #[inline]
    pub fn swap_remove(&mut self, index: K) -> V
    where
        K: Into<usize>,
    {
        self.raw.swap_remove(index.into())
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// See [`Vec::insert`] for more details.
    ///
    /// [`Vec::insert`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.insert
    #[inline]
    pub fn insert(&mut self, index: K, element: V)
    where
        K: Into<usize>,
    {
        self.raw.insert(index.into(), element);
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// See [`Vec::remove`] for more details.
    ///
    /// [`Vec::remove`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.remove
    #[inline]
    pub fn remove(&mut self, index: K) -> V
    where
        K: Into<usize>,
    {
        self.raw.remove(index.into())
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// See [`Vec::retain`] for more details.
    ///
    /// [`Vec::retain`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.retain
    #[inline]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.retain(f);
    }

    /// Retains only the elements specified by the predicate, passing a mutable
    /// reference to it.
    ///
    /// See [`Vec::retain_mut`] for more details.
    ///
    /// [`Vec::retain_mut`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.retain_mut
    #[inline]
    pub fn retain_mut<F>(&mut self, f: F)
    where
        F: FnMut(&mut V) -> bool,
    {
        self.raw.retain_mut(f);
    }

    /// Removes all but the first of consecutive elements in the vector that
    /// resolve to the same key.
    ///
    /// See [`Vec::dedup_by_key`] for more details.
    ///
    /// [`Vec::dedup_by_key`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.dedup_by_key
    #[inline]
    pub fn dedup_by_key<F, K2>(&mut self, key: F)
    where
        F: FnMut(&mut V) -> K2,
        K2: PartialEq,
    {
        self.raw.dedup_by_key(key);
    }

    /// Removes all but the first of consecutive elements in the vector
    /// satisfying a given equality relation.
    ///
    /// See [`Vec::dedup_by`] for more details.
    ///
    /// [`Vec::dedup_by`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.dedup_by
    #[inline]
    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut V, &mut V) -> bool,
    {
        self.raw.dedup_by(same_bucket);
    }

    /// Appends an element to the back of a collection.
    ///
    /// See [`Vec::push`] for more details.
    ///
    /// [`Vec::push`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.push
    #[inline]
    pub fn push(&mut self, value: V) {
        self.raw.push(value);
    }

    /// Appends an element to the back of a collection and returns its index of
    /// type `K`.
    ///
    /// It acts like `{ vec.push(...); vec.last_key().unwrap() }`,
    /// but is optimized better.
    ///
    /// See [`Vec::push`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiVec;
    /// #[derive(Eq, Debug, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let mut vec: TiVec<Id, usize> = vec![1, 2, 4].into();
    /// assert_eq!(vec.push_and_get_key(8), Id(3));
    /// assert_eq!(vec.push_and_get_key(16), Id(4));
    /// assert_eq!(vec.push_and_get_key(32), Id(5));
    /// ```
    ///
    /// [`Vec::push`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.push
    #[inline]
    pub fn push_and_get_key(&mut self, value: V) -> K
    where
        usize: Into<K>,
    {
        let key = self.next_key();
        self.raw.push(value);
        key
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it
    /// is empty.
    ///
    /// See [`Vec::pop`] for more details.
    ///
    /// [`Vec::pop`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.pop
    #[inline]
    pub fn pop(&mut self) -> Option<V> {
        self.raw.pop()
    }

    /// Removes the last element from a vector and returns it with
    /// its index of type `K`, or [`None`] if the vector is empty.
    ///
    /// See [`Vec::pop`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiVec;
    /// #[derive(Eq, Debug, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let mut vec: TiVec<Id, usize> = vec![1, 2, 4].into();
    /// assert_eq!(vec.pop_key_value(), Some((Id(2), 4)));
    /// assert_eq!(vec.pop_key_value(), Some((Id(1), 2)));
    /// assert_eq!(vec.pop_key_value(), Some((Id(0), 1)));
    /// assert_eq!(vec.pop_key_value(), None);
    /// ```
    ///
    /// [`Vec::pop`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.pop
    #[inline]
    pub fn pop_key_value(&mut self) -> Option<(K, V)>
    where
        usize: Into<K>,
    {
        self.raw.pop().map(|value| (self.raw.len().into(), value))
    }

    /// Removes and returns the last element from a vector if the predicate
    /// returns `true`, or [`None`] if the predicate returns false or the vector
    /// is empty (the predicate will not be called in that case).
    ///
    /// See [`Vec::pop_if`] for more details.
    ///
    /// [`Vec::pop_if`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.pop_if
    #[inline]
    pub fn pop_if(&mut self, predicate: impl FnOnce(&mut V) -> bool) -> Option<V> {
        self.raw.pop_if(predicate)
    }

    /// Removes and returns the last element from a vector if the predicate
    /// returns `true` with its index of type `K`, or [`None`] if the predicate
    /// returns false or the vector is empty (the predicate will not be called
    /// in that case).
    ///
    /// See [`Vec::pop_if`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiVec;
    /// #[derive(Eq, Debug, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let mut vec: TiVec<Id, i32> = vec![-2, 4].into();
    /// assert_eq!(vec.pop_key_value_if(|v| *v > 0), Some((Id(1), 4)));
    /// assert_eq!(vec.pop_key_value_if(|v| *v > 0), None);
    /// assert_eq!(vec.pop_key_value_if(|v| *v < 0), Some((Id(0), -2)));
    /// assert_eq!(vec.pop_key_value_if(|v| *v < 0), None);
    /// assert_eq!(vec.pop_key_value_if(|v| *v > 0), None);
    /// ```
    ///
    /// [`Vec::pop_if`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.pop_if
    #[inline]
    pub fn pop_key_value_if(&mut self, predicate: impl FnOnce(&mut V) -> bool) -> Option<(K, V)>
    where
        usize: Into<K>,
    {
        self.raw
            .pop_if(predicate)
            .map(|value| (self.raw.len().into(), value))
    }

    /// Moves all the elements of `other` into `Self`, leaving `other` empty.
    ///
    /// See [`Vec::append`] for more details.
    ///
    /// [`Vec::append`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.append
    #[inline]
    pub fn append(&mut self, other: &mut Self) {
        self.raw.append(&mut other.raw);
    }

    /// Creates a draining iterator that removes the specified range in the
    /// vector and yields the removed items.
    ///
    /// See [`Vec::drain`] for more details.
    ///
    /// [`Vec::drain`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.drain
    #[cfg(feature = "nightly")]
    #[inline]
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, V, A>
    where
        R: TiRangeBounds<K>,
    {
        self.raw.drain(range.into_range())
    }

    /// Creates a draining iterator that removes the specified range in the
    /// vector and yields the removed items.
    ///
    /// See [`Vec::drain`] for more details.
    ///
    /// [`Vec::drain`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.drain
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, V>
    where
        R: TiRangeBounds<K>,
    {
        self.raw.drain(range.into_range())
    }

    /// Creates a draining iterator that removes the specified
    /// range in the vector and yields the current count and the removed items.
    ///
    /// It acts like `self.drain(range).enumerate()`,
    /// but instead of `usize` it returns index of type `K`.
    ///
    /// Note that the indices started from `K::from_usize(0)`,
    /// regardless of the range starting point.
    ///
    /// See [`Vec::drain`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::{TiSlice, TiVec};
    /// #[derive(Eq, Debug, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let mut vec: TiVec<Id, usize> = vec![1, 2, 4].into();
    /// {
    ///     let mut iterator = vec.drain_enumerated(Id(1)..);
    ///     assert_eq!(iterator.next(), Some((Id(0), 2)));
    ///     assert_eq!(iterator.next(), Some((Id(1), 4)));
    ///     assert_eq!(iterator.next(), None);
    /// }
    /// assert_eq!(vec.as_slice(), TiSlice::from_ref(&[1]));
    /// ```
    ///
    /// [`Vec::drain`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.drain
    #[cfg(feature = "nightly")]
    #[inline]
    pub fn drain_enumerated<R>(&mut self, range: R) -> TiEnumerated<Drain<'_, V, A>, K, V>
    where
        usize: Into<K>,
        R: TiRangeBounds<K>,
    {
        self.raw
            .drain(range.into_range())
            .enumerate()
            .map(|(key, value)| (key.into(), value))
    }

    /// Creates a draining iterator that removes the specified
    /// range in the vector and yields the current count and the removed items.
    ///
    /// It acts like `self.drain(range).enumerate()`,
    /// but instead of `usize` it returns index of type `K`.
    ///
    /// Note that the indices started from `K::from_usize(0)`,
    /// regardless of the range starting point.
    ///
    /// See [`Vec::drain`] for more details.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::{TiSlice, TiVec};
    /// #[derive(Eq, Debug, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let mut vec: TiVec<Id, usize> = vec![1, 2, 4].into();
    /// {
    ///     let mut iterator = vec.drain_enumerated(Id(1)..);
    ///     assert_eq!(iterator.next(), Some((Id(0), 2)));
    ///     assert_eq!(iterator.next(), Some((Id(1), 4)));
    ///     assert_eq!(iterator.next(), None);
    /// }
    /// assert_eq!(vec.as_slice(), TiSlice::from_ref(&[1]));
    /// ```
    ///
    /// [`Vec::drain`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.drain
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn drain_enumerated<R>(&mut self, range: R) -> TiEnumerated<Drain<'_, V>, K, V>
    where
        usize: Into<K>,
        R: TiRangeBounds<K>,
    {
        self.raw
            .drain(range.into_range())
            .enumerate()
            .map(|(key, value)| (key.into(), value))
    }

    /// Clears the vector, removing all values.
    ///
    /// See [`Vec::clear`] for more details.
    ///
    /// [`Vec::clear`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.clear
    #[inline]
    pub fn clear(&mut self) {
        self.raw.clear();
    }

    /// Returns the number of elements in the vector, also referred to
    /// as its 'length'.
    ///
    /// See [`Vec::len`] for more details.
    ///
    /// [`Vec::len`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.len
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.raw.len()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// See [`Vec::is_empty`] for more details.
    ///
    /// [`Vec::is_empty`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.is_empty
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    /// Splits the collection into two at the given index.
    ///
    /// See [`Vec::split_off`] for more details.
    ///
    /// [`Vec::split_off`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.split_off
    #[inline]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off(&mut self, at: K) -> Self
    where
        K: Into<usize>,
        A: Clone,
    {
        self.raw.split_off(at.into()).into()
    }

    /// Resizes the `TiVec` in-place so that `len` is equal to `new_len`.
    ///
    /// See [`Vec::resize_with`] for more details.
    ///
    /// [`Vec::resize_with`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.resize_with
    #[inline]
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> V,
    {
        self.raw.resize_with(new_len, f);
    }

    /// Resizes the `TiVec` in-place so that `len` is equal to `new_len`.
    ///
    /// See [`Vec::resize`] for more details.
    ///
    /// [`Vec::resize`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.resize
    #[inline]
    pub fn resize(&mut self, new_len: usize, value: V)
    where
        V: Clone,
    {
        self.raw.resize(new_len, value);
    }

    /// Consumes and leaks the `Vec`, returning a mutable reference to the
    /// contents, `&'a mut [T]`. Note that the type `T` must outlive the
    /// chosen lifetime `'a`. If the type has only static references, or
    /// none at all, then this may be chosen to be `'static`.
    ///
    /// See [`Vec::leak`] for more details.
    ///
    /// [`Vec::leak`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.leak
    #[allow(
        clippy::allow_attributes,
        clippy::must_use_candidate,
        reason = "not used in `Vec::leak`"
    )]
    #[inline]
    pub fn leak<'a>(self) -> &'a mut TiSlice<K, V>
    where
        A: 'a,
    {
        self.raw.leak().as_mut()
    }

    /// Returns the remaining spare capacity of the vector as a slice of
    /// `MaybeUninit<T>`.
    ///
    /// See [`Vec::spare_capacity_mut`] for more details.
    ///
    /// [`Vec::spare_capacity_mut`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.spare_capacity_mut
    #[inline]
    pub fn spare_capacity_mut(&mut self) -> &mut TiSlice<K, MaybeUninit<V>> {
        self.raw.spare_capacity_mut().as_mut()
    }

    /// Clones and appends all elements in a slice to the `TiVec`.
    ///
    /// See [`Vec::extend_from_slice`] for more details.
    ///
    /// [`Vec::extend_from_slice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.extend_from_slice
    #[inline]
    pub fn extend_from_slice(&mut self, other: &TiSlice<K, V>)
    where
        V: Clone,
    {
        self.raw.extend_from_slice(&other.raw);
    }

    /// Copies elements from `src` range to the end of the vector.
    ///
    /// See [`Vec::extend_from_within`] for more details.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// [`Vec::extend_from_within`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.extend_from_within
    /// [`extend_from_within`]: #method.extend_from_within
    #[inline]
    pub fn extend_from_within<R>(&mut self, src: R)
    where
        V: Clone,
        R: TiRangeBounds<K>,
    {
        self.raw.extend_from_within(src.into_range());
    }

    /// Removes consecutive repeated elements in the vector according to the
    /// [`PartialEq`] trait implementation.
    ///
    /// See [`Vec::dedup`] for more details.
    ///
    /// [`PartialEq`]: https://doc.rust-lang.org/std/cmp/trait.PartialEq.html
    /// [`Vec::dedup`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.dedup
    #[inline]
    pub fn dedup(&mut self)
    where
        V: PartialEq,
    {
        self.raw.dedup();
    }

    /// Creates a splicing iterator that replaces the specified range in the
    /// vector with the given `replace_with` iterator and yields the removed
    /// items. `replace_with` does not need to be the same length as
    /// `range`.
    ///
    /// See [`Vec::splice`] for more details.
    ///
    /// [`Vec::splice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.splice
    #[cfg(feature = "nightly")]
    #[inline]
    pub fn splice<R, I>(&mut self, range: R, replace_with: I) -> Splice<'_, I::IntoIter, A>
    where
        R: TiRangeBounds<K>,
        I: IntoIterator<Item = V>,
    {
        self.raw.splice(range.into_range(), replace_with)
    }

    /// Creates a splicing iterator that replaces the specified range in the
    /// vector with the given `replace_with` iterator and yields the removed
    /// items. `replace_with` does not need to be the same length as
    /// `range`.
    ///
    /// See [`Vec::splice`] for more details.
    ///
    /// [`Vec::splice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.splice
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn splice<R, I>(&mut self, range: R, replace_with: I) -> Splice<'_, I::IntoIter>
    where
        R: TiRangeBounds<K>,
        I: IntoIterator<Item = V>,
    {
        self.raw.splice(range.into_range(), replace_with)
    }

    /// Converts the vector into iterator over all key-value pairs
    /// with `K` used for iteration indices.
    ///
    /// It acts like `self.into_iter().enumerate()`,
    /// but use `K` instead of `usize` for iteration indices.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiVec;
    /// #[derive(Eq, Debug, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let vec: TiVec<Id, usize> = vec![1, 2, 4].into();
    /// let mut iterator = vec.into_iter_enumerated();
    /// assert_eq!(iterator.next(), Some((Id(0), 1)));
    /// assert_eq!(iterator.next(), Some((Id(1), 2)));
    /// assert_eq!(iterator.next(), Some((Id(2), 4)));
    /// assert_eq!(iterator.next(), None);
    /// ```
    #[cfg(feature = "nightly")]
    #[inline]
    pub fn into_iter_enumerated(self) -> TiEnumerated<vec::IntoIter<V, A>, K, V>
    where
        usize: Into<K>,
    {
        self.raw
            .into_iter()
            .enumerate()
            .map(|(key, value)| (key.into(), value))
    }

    /// Converts the vector into iterator over all key-value pairs
    /// with `K` used for iteration indices.
    ///
    /// It acts like `self.into_iter().enumerate()`,
    /// but use `K` instead of `usize` for iteration indices.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiVec;
    /// #[derive(Eq, Debug, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let vec: TiVec<Id, usize> = vec![1, 2, 4].into();
    /// let mut iterator = vec.into_iter_enumerated();
    /// assert_eq!(iterator.next(), Some((Id(0), 1)));
    /// assert_eq!(iterator.next(), Some((Id(1), 2)));
    /// assert_eq!(iterator.next(), Some((Id(2), 4)));
    /// assert_eq!(iterator.next(), None);
    /// ```
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn into_iter_enumerated(self) -> TiEnumerated<vec::IntoIter<V>, K, V>
    where
        usize: Into<K>,
    {
        self.raw
            .into_iter()
            .enumerate()
            .map(|(key, value)| (key.into(), value))
    }
}

impl<K, V, A: Allocator> fmt::Debug for TiVec<K, V, A>
where
    K: fmt::Debug,
    V: fmt::Debug,
    usize: Into<K>,
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

impl<K, V, A: Allocator> AsRef<Self> for TiVec<K, V, A> {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<K, V, A: Allocator> AsMut<Self> for TiVec<K, V, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<K, V, A: Allocator> AsRef<TiSlice<K, V>> for TiVec<K, V, A> {
    #[inline]
    fn as_ref(&self) -> &TiSlice<K, V> {
        self
    }
}

impl<K, V, A: Allocator> AsMut<TiSlice<K, V>> for TiVec<K, V, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut TiSlice<K, V> {
        self
    }
}

#[cfg(feature = "nightly")]
impl<K, V, A: Allocator> AsRef<Vec<V, A>> for TiVec<K, V, A> {
    #[inline]
    fn as_ref(&self) -> &Vec<V, A> {
        &self.raw
    }
}

#[cfg(not(feature = "nightly"))]
impl<K, V, A: Allocator> AsRef<Vec<V>> for TiVec<K, V, A> {
    #[inline]
    fn as_ref(&self) -> &Vec<V> {
        &self.raw
    }
}

#[cfg(feature = "nightly")]
impl<K, V, A: Allocator> AsMut<Vec<V, A>> for TiVec<K, V, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut Vec<V, A> {
        &mut self.raw
    }
}

#[cfg(not(feature = "nightly"))]
impl<K, V, A: Allocator> AsMut<Vec<V>> for TiVec<K, V, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut Vec<V> {
        &mut self.raw
    }
}

impl<K, V, A: Allocator> AsRef<[V]> for TiVec<K, V, A> {
    #[inline]
    fn as_ref(&self) -> &[V] {
        &self.raw
    }
}

impl<K, V, A: Allocator> AsMut<[V]> for TiVec<K, V, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut [V] {
        &mut self.raw
    }
}

#[cfg(feature = "nightly")]
impl<K, V, A: Allocator> AsRef<TiVec<K, V, A>> for Vec<V, A> {
    #[inline]
    fn as_ref(&self) -> &TiVec<K, V, A> {
        TiVec::from_ref(self)
    }
}

#[cfg(not(feature = "nightly"))]
impl<K, V> AsRef<TiVec<K, V>> for Vec<V> {
    #[inline]
    fn as_ref(&self) -> &TiVec<K, V> {
        TiVec::from_ref(self)
    }
}

#[cfg(feature = "nightly")]
impl<K, V, A: Allocator> AsMut<TiVec<K, V, A>> for Vec<V, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut TiVec<K, V, A> {
        TiVec::from_mut(self)
    }
}

#[cfg(not(feature = "nightly"))]
impl<K, V> AsMut<TiVec<K, V>> for Vec<V> {
    #[inline]
    fn as_mut(&mut self) -> &mut TiVec<K, V> {
        TiVec::from_mut(self)
    }
}

impl<K, V, A: Allocator> Borrow<TiSlice<K, V>> for TiVec<K, V, A> {
    #[inline]
    fn borrow(&self) -> &TiSlice<K, V> {
        self.as_slice()
    }
}

impl<K, V, A: Allocator> BorrowMut<TiSlice<K, V>> for TiVec<K, V, A> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut TiSlice<K, V> {
        self.as_mut_slice()
    }
}

impl<K, V, A: Allocator> Deref for TiVec<K, V, A> {
    type Target = TiSlice<K, V>;

    #[inline]
    fn deref(&self) -> &TiSlice<K, V> {
        Self::Target::from_ref(&self.raw)
    }
}

impl<K, V, A: Allocator> DerefMut for TiVec<K, V, A> {
    #[inline]
    fn deref_mut(&mut self) -> &mut TiSlice<K, V> {
        Self::Target::from_mut(&mut self.raw)
    }
}

#[cfg(feature = "nightly")]
impl<K, V, A: Allocator> From<Vec<V, A>> for TiVec<K, V, A> {
    #[inline]
    fn from(vec: Vec<V, A>) -> Self {
        Self {
            raw: vec,
            _marker: PhantomData,
            #[cfg(not(feature = "nightly"))]
            _alloc: PhantomData,
        }
    }
}

#[cfg(not(feature = "nightly"))]
impl<K, V, A: Allocator> From<Vec<V>> for TiVec<K, V, A> {
    #[inline]
    fn from(vec: Vec<V>) -> Self {
        Self {
            raw: vec,
            _marker: PhantomData,
            #[cfg(not(feature = "nightly"))]
            _alloc: PhantomData,
        }
    }
}

#[cfg(feature = "nightly")]
impl<K, V, A: Allocator> From<TiVec<K, V, A>> for Vec<V, A> {
    #[inline]
    fn from(vec: TiVec<K, V, A>) -> Self {
        vec.raw
    }
}

#[cfg(not(feature = "nightly"))]
impl<K, V> From<TiVec<K, V>> for Vec<V> {
    #[inline]
    fn from(vec: TiVec<K, V>) -> Self {
        vec.raw
    }
}

impl<K, V> From<&TiSlice<K, V>> for TiVec<K, V>
where
    V: Clone,
{
    #[inline]
    fn from(slice: &TiSlice<K, V>) -> Self {
        slice.to_vec()
    }
}

impl<K, V> From<&mut TiSlice<K, V>> for TiVec<K, V>
where
    V: Clone,
{
    #[inline]
    fn from(slice: &mut TiSlice<K, V>) -> Self {
        slice.to_vec()
    }
}

impl<K, V> From<Cow<'_, TiSlice<K, V>>> for TiVec<K, V>
where
    V: Clone,
{
    #[inline]
    fn from(slice: Cow<'_, TiSlice<K, V>>) -> Self {
        slice.into_owned()
    }
}

impl<K, V> From<TiVec<K, V>> for Cow<'_, TiSlice<K, V>>
where
    V: Clone,
{
    #[inline]
    fn from(vec: TiVec<K, V>) -> Self {
        Cow::Owned(vec)
    }
}

impl<K> From<&str> for TiVec<K, u8> {
    #[inline]
    fn from(s: &str) -> Self {
        s.as_bytes().to_vec().into()
    }
}

impl<K> From<String> for TiVec<K, u8> {
    #[inline]
    fn from(s: String) -> Self {
        s.into_bytes().into()
    }
}

impl<K> From<CString> for TiVec<K, u8> {
    #[inline]
    fn from(s: CString) -> Self {
        s.into_bytes().into()
    }
}

impl<K, V, A> Clone for TiVec<K, V, A>
where
    V: Clone,
    A: Allocator + Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        self.raw.clone().into()
    }
}

impl<K, V, A: Allocator> Eq for TiVec<K, V, A> where V: Eq {}

impl<K, V1, V2, A: Allocator> PartialEq<TiVec<K, V2, A>> for TiVec<K, V1, A>
where
    V1: PartialEq<V2>,
{
    #[inline]
    fn eq(&self, other: &TiVec<K, V2, A>) -> bool {
        self.raw == other.raw
    }
}

impl<K, V1, V2, A: Allocator> PartialEq<TiSlice<K, V2>> for TiVec<K, V1, A>
where
    V1: PartialEq<V2>,
{
    #[inline]
    fn eq(&self, other: &TiSlice<K, V2>) -> bool {
        *self.raw == other.raw
    }
}

impl<K, V1, V2, A: Allocator> PartialEq<TiVec<K, V2, A>> for TiSlice<K, V1>
where
    V1: PartialEq<V2>,
{
    #[inline]
    fn eq(&self, other: &TiVec<K, V2, A>) -> bool {
        self.raw == *other.raw
    }
}

impl<'a, K, V1, V2, A: Allocator> PartialEq<&'a TiSlice<K, V2>> for TiVec<K, V1, A>
where
    V1: PartialEq<V2>,
{
    #[inline]
    fn eq(&self, other: &&'a TiSlice<K, V2>) -> bool {
        *self.raw == other.raw
    }
}

impl<K, V1, V2, A: Allocator> PartialEq<TiVec<K, V2, A>> for &TiSlice<K, V1>
where
    V1: PartialEq<V2>,
{
    #[inline]
    fn eq(&self, other: &TiVec<K, V2, A>) -> bool {
        self.raw == *other.raw
    }
}

impl<'a, K, V1, V2, A: Allocator> PartialEq<&'a mut TiSlice<K, V2>> for TiVec<K, V1, A>
where
    V1: PartialEq<V2>,
{
    #[inline]
    fn eq(&self, other: &&'a mut TiSlice<K, V2>) -> bool {
        *self.raw == other.raw
    }
}

impl<K, V1, V2, A: Allocator> PartialEq<TiVec<K, V2, A>> for &mut TiSlice<K, V1>
where
    V1: PartialEq<V2>,
{
    #[inline]
    fn eq(&self, other: &TiVec<K, V2, A>) -> bool {
        self.raw == *other.raw
    }
}

impl<K, V, A: Allocator> Ord for TiVec<K, V, A>
where
    V: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.raw.cmp(&other.raw)
    }
}

impl<K, V, A: Allocator> PartialOrd<Self> for TiVec<K, V, A>
where
    V: PartialOrd<V>,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.raw.partial_cmp(&other.raw)
    }
}

impl<K, V, A: Allocator> Hash for TiVec<K, V, A>
where
    V: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

impl<K, V> Default for TiVec<K, V> {
    #[inline]
    fn default() -> Self {
        Vec::default().into()
    }
}

impl<I, K, V, A: Allocator> Index<I> for TiVec<K, V, A>
where
    I: TiSliceIndex<K, V>,
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        index.index(self)
    }
}

impl<I, K, V, A: Allocator> IndexMut<I> for TiVec<K, V, A>
where
    I: TiSliceIndex<K, V>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        index.index_mut(self)
    }
}

impl<K, V, A: Allocator> Extend<V> for TiVec<K, V, A> {
    #[inline]
    fn extend<I: IntoIterator<Item = V>>(&mut self, iter: I) {
        self.raw.extend(iter);
    }
}

impl<'a, K, V: 'a + Copy, A: Allocator> Extend<&'a V> for TiVec<K, V, A> {
    #[inline]
    fn extend<I: IntoIterator<Item = &'a V>>(&mut self, iter: I) {
        self.raw.extend(iter);
    }
}

impl<K, V> FromIterator<V> for TiVec<K, V> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        Self {
            raw: Vec::from_iter(iter),
            _marker: PhantomData,
            #[cfg(not(feature = "nightly"))]
            _alloc: PhantomData,
        }
    }
}

#[cfg(feature = "nightly")]
impl<K, V, A: Allocator> IntoIterator for TiVec<K, V, A> {
    type Item = V;
    type IntoIter = vec::IntoIter<V, A>;

    #[inline]
    fn into_iter(self) -> vec::IntoIter<V, A> {
        self.raw.into_iter()
    }
}

#[cfg(not(feature = "nightly"))]
impl<K, V> IntoIterator for TiVec<K, V> {
    type Item = V;
    type IntoIter = vec::IntoIter<V>;

    #[inline]
    fn into_iter(self) -> vec::IntoIter<V> {
        self.raw.into_iter()
    }
}

impl<'a, K, V> IntoIterator for &'a TiVec<K, V> {
    type Item = &'a V;
    type IntoIter = slice::Iter<'a, V>;

    #[inline]
    fn into_iter(self) -> slice::Iter<'a, V> {
        self.raw.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut TiVec<K, V> {
    type Item = &'a mut V;
    type IntoIter = slice::IterMut<'a, V>;

    #[inline]
    fn into_iter(self) -> slice::IterMut<'a, V> {
        self.raw.iter_mut()
    }
}

/// Write is implemented for `Vec<u8>` by appending to the vector.
/// The vector will grow as needed.
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<K> Write for TiVec<K, u8> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> IoResult<usize> {
        self.raw.write(buf)
    }

    #[inline]
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> IoResult<usize> {
        self.raw.write_vectored(bufs)
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> IoResult<()> {
        self.raw.write_all(buf)
    }

    #[inline]
    fn flush(&mut self) -> IoResult<()> {
        self.raw.flush()
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<K, V, A: Allocator> Serialize for TiVec<K, V, A>
where
    V: Serialize,
{
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.raw.as_slice().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<'de, K, V> Deserialize<'de> for TiVec<K, V>
where
    V: Deserialize<'de>,
{
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Vec::deserialize(deserializer).map(Into::into)
    }
}

#[cfg(feature = "bincode")]
#[cfg_attr(docsrs, doc(cfg(feature = "bincode")))]
impl<K, V, A: Allocator> Encode for TiVec<K, V, A>
where
    V: Encode,
{
    #[inline]
    fn encode<E>(&self, encoder: &mut E) -> Result<(), EncodeError>
    where
        E: Encoder,
    {
        self.raw.encode(encoder)
    }
}

#[cfg(feature = "bincode")]
#[cfg_attr(docsrs, doc(cfg(feature = "bincode")))]
impl<K, V, Context> Decode<Context> for TiVec<K, V>
where
    V: Decode<Context>,
{
    #[inline]
    fn decode<D>(decoder: &mut D) -> Result<Self, DecodeError>
    where
        D: Decoder<Context = Context>,
    {
        Vec::decode(decoder).map(Into::into)
    }
}

#[cfg(feature = "bincode")]
#[cfg_attr(docsrs, doc(cfg(feature = "bincode")))]
impl<'de, K, V, Context> BorrowDecode<'de, Context> for TiVec<K, V>
where
    V: BorrowDecode<'de, Context>,
{
    #[inline]
    fn borrow_decode<D>(decoder: &mut D) -> Result<Self, DecodeError>
    where
        D: BorrowDecoder<'de, Context = Context>,
    {
        Vec::borrow_decode(decoder).map(Into::into)
    }
}

#[expect(
    dead_code,
    unused_imports,
    unused_mut,
    clippy::into_iter_on_ref,
    clippy::op_ref,
    clippy::too_many_lines,
    clippy::undocumented_unsafe_blocks,
    clippy::unwrap_used,
    reason = "okay in tests"
)]
#[rustversion::attr(
    since(1.99.0),
    expect(clippy::mut_mut, reason = "macro generated code"),
)]
#[cfg(test)]
mod test {
    use alloc::borrow::{Cow, ToOwned};
    use alloc::boxed::Box;
    use alloc::ffi::CString;
    use alloc::string::ToString;
    use alloc::vec::Vec;
    use core::borrow::{Borrow, BorrowMut};
    use core::hash::{Hash, Hasher};
    use core::ops::Bound;
    #[cfg(feature = "std")]
    use std::hash::DefaultHasher;
    #[cfg(feature = "std")]
    use std::io::{IoSlice, Write};

    use crate::test_util::{AsSliceAndCapacity, Id};
    use crate::{TiSlice, TiVec};

    #[test]
    fn test_vec_read_api_compatibility() {
        assert_eq!(
            TiVec::<Id, u32>::new().as_slice_and_capacity(),
            Vec::<u32>::new().as_slice_and_capacity(),
        );
        for c in [0, 1, 2, 4] {
            assert_eq!(
                TiVec::<Id, u32>::with_capacity(c).as_slice_and_capacity(),
                Vec::<u32>::with_capacity(c).as_slice_and_capacity(),
            );
        }

        for v in [
            &[0_u32; 0][..],
            &[1],
            &[1, 1234],
            &[1, 2, 4],
            &[1, 5, 3, 2],
            &[1, 1, 9, 2, 4, 1, 12345, 12],
        ] {
            let cv = (v.to_vec(), TiVec::<Id, _>::from(v.to_vec()));
            let mut cv = (&cv.0, &cv.1);

            let mut mv = (v.to_vec(), TiVec::<Id, _>::from(v.to_vec()));
            let mut mv = (&mut mv.0, &mut mv.1);

            assert_eq_api!(cv, v => AsRef::<[_]>::as_ref(v));
            assert_eq_api!(mv, v => AsMut::<[_]>::as_mut(v));
            assert_eq_api!(cv, v => AsRef::<Vec<_>>::as_ref(v));
            assert_eq_api!(mv, v => AsMut::<Vec<_>>::as_mut(v));
            assert_eq_api!(cv, v => AsRef::<TiVec<_, _>>::as_ref(v));
            assert_eq_api!(mv, v => AsMut::<TiVec<_, _>>::as_mut(v));
            assert_eq!(
                AsRef::<[_]>::as_ref(cv.0),
                AsRef::<[_]>::as_ref(AsRef::<TiSlice<_, _>>::as_ref(cv.1))
            );
            assert_eq!(
                AsMut::<[_]>::as_mut(mv.0),
                AsMut::<[_]>::as_mut(AsMut::<TiSlice<_, _>>::as_mut(mv.1))
            );
            assert_eq!(
                Borrow::<[_]>::borrow(cv.0),
                AsRef::<[_]>::as_ref(Borrow::<TiSlice<_, _>>::borrow(cv.1))
            );
            assert_eq!(
                BorrowMut::<[_]>::borrow_mut(mv.0),
                AsMut::<[_]>::as_mut(BorrowMut::<TiSlice<_, _>>::borrow_mut(mv.1))
            );

            assert_eq_api!(cv, v => v.len());
            assert_eq_api!(cv, v => v.is_empty());
            assert_eq_api!(cv, v => v.capacity());
            assert_eq_api!(cv, v => v.as_slice().into_std());
            assert_eq_api!(mv, v => v.as_mut_slice().into_std());
            assert_eq_api!(cv, v => TheVec::from(v.as_slice()).into_std());
            assert_eq_api!(mv, v => TheVec::from(v.as_mut_slice()).into_std());
            assert_eq_api!(cv, v => TheVec::from(Cow::Borrowed(v.as_slice())).into_std());
            assert_eq_api!(mv, v => Cow::from(v.clone()).into_std());

            if !v.is_empty() {
                assert_ne!(cv.0.as_ptr(), cv.1.as_ptr());
                assert_ne!(cv.0.as_ptr_range(), cv.1.as_ptr_range());
                assert_ne!(mv.0.as_mut_ptr(), mv.1.as_mut_ptr());
                assert_ne!(mv.0.as_mut_ptr_range(), mv.1.as_mut_ptr_range());
            }

            assert_eq_api!(cv, v => *v == TheVec::<u32>::default());
            assert_eq_api!(cv, v => v == v.as_slice());
            assert_eq_api!(cv, v => v.as_slice() == v);
            assert_eq_api!(cv, v => v == &v.as_slice());
            assert_eq_api!(cv, v => &v.as_slice() == v);
            assert_eq_api!(mv, v => v == &(&mut [1_u32, 1234][..]).into_tic());
            assert_eq_api!(mv, v => &(&mut [1_u32, 1234][..]).into_tic() == v);
            assert_eq_api!(cv, v => v.cmp(&alloc::vec![1, 1234].into_tic()));
            assert_eq_api!(cv, v => v.partial_cmp(&alloc::vec![1, 1234].into_tic()));

            for i in 0..v.len() {
                assert_eq_api!(cv, v => v[i.into_tic()]);
                assert_eq_api!(mv, v => v[i.into_tic()] = v[i.into_tic()]);
            }

            unsafe {
                assert_eq_api!(cv, v => {
                    let mut v = core::mem::ManuallyDrop::new(v.clone());
                    TheVec::from_raw_parts(v.as_mut_ptr(), v.len(), v.capacity()).into_std()
                });
            }
        }
    }

    #[rustversion::since(1.93.0)]
    #[test]
    fn test_vec_read_api_compatibility_since_1_93() {
        for v in [
            &[0_u32; 0][..],
            &[1],
            &[1, 1234],
            &[1, 2, 4],
            &[1, 5, 3, 2],
            &[1, 1, 9, 2, 4, 1, 12345, 12],
        ] {
            let cv = (v.to_vec(), TiVec::<Id, _>::from(v.to_vec()));
            let mut cv = (&cv.0, &cv.1);

            assert_eq_api!(cv, v => v.clone().into_raw_parts().1);
            assert_eq_api!(cv, v => v.clone().into_raw_parts().2);

            if !v.is_empty() {
                assert_ne!(
                    cv.0.clone().into_raw_parts().0,
                    cv.1.clone().into_raw_parts().0
                );
            }
        }
    }

    #[test]
    fn test_vec_write_api_compatibility() {
        for v in [
            &[0_u32; 0][..],
            &[1],
            &[1, 1234],
            &[1, 2, 4],
            &[1, 5, 3, 2],
            &[1, 1, 9, 2, 4, 1, 12345, 12],
        ] {
            let mut mv = (v.to_vec(), TiVec::<Id, _>::from(v.to_vec()));
            let mut mv = (&mut mv.0, &mut mv.1);

            let restore = |mv: &mut (&mut Vec<u32>, &mut TiVec<Id, u32>)| {
                *mv.0 = v.to_vec();
                *mv.1 = TiVec::from(v.to_vec());
            };

            restore(&mut mv);
            assert_eq_api!(mv, v => v.try_reserve(usize::MAX));
            restore(&mut mv);
            assert_eq_api!(mv, v => v.try_reserve_exact(usize::MAX));

            for i in 0..8 {
                restore(&mut mv);
                assert_eq_api!(mv, v => v.resize(i, 123));
                restore(&mut mv);
                assert_eq_api!(mv, v => { let mut a = 1; v.resize_with(i, || { a *= 2; a }) });
                restore(&mut mv);
                assert_eq_api!(mv, v => v.reserve(i));
                assert_eq_api!(mv, v => v.spare_capacity_mut().len());
                restore(&mut mv);
                assert_eq_api!(mv, v => v.try_reserve(i));
                restore(&mut mv);
                assert_eq_api!(mv, v => v.reserve_exact(i));
                restore(&mut mv);
                assert_eq_api!(mv, v => v.try_reserve_exact(i));
                restore(&mut mv);
                assert_eq_api!(mv, v => v.reserve_exact(i));
                assert_eq_api!(mv, v => v.shrink_to_fit());
                restore(&mut mv);
                assert_eq_api!(mv, v => v.reserve_exact(i * 2));
                assert_eq_api!(mv, v => v.shrink_to(i));
                restore(&mut mv);
                assert_eq_api!(mv, v => v.truncate(i));
            }

            let l1: Vec<_> = mv.0.clone();
            let l1c = l1.capacity();
            let l1 = l1.leak();
            let l2: TiVec<_, _> = mv.1.clone();
            let l2c = l2.capacity();
            let l2 = l2.leak();
            assert_eq!(l1, &l2.raw);
            drop(unsafe { Vec::from_raw_parts(l1.as_mut_ptr(), l1.len(), l1c) });
            drop(unsafe { TiVec::<Id, _>::from_raw_parts(l2.as_mut_ptr(), l2.len(), l2c) });

            restore(&mut mv);
            assert_eq_api!(mv, v => (&*v).into_iter().copied().collect::<Vec<_>>());
            assert_eq_api!(mv, v => v.iter_mut().collect::<Vec<_>>());
            assert_eq_api!(mv, v => v.clone().into_iter().collect::<Vec<_>>());

            restore(&mut mv);
            assert_eq_api!(mv, v => v.pop());
            assert_eq_api!(mv, v => v.push(123));
            assert_eq_api!(mv, v => v.pop());

            restore(&mut mv);
            assert_eq_api!(mv, v => v.pop_if(|v| *v < 10));
            assert_eq_api!(mv, v => v.push(234));

            restore(&mut mv);
            assert_eq_api!(mv, v => v.append(&mut v.clone()));
            restore(&mut mv);
            assert_eq_api!(mv, v => v.extend(v.clone().as_slice()));
            restore(&mut mv);
            assert_eq_api!(mv, v => v.extend(v.clone().iter().copied()));
            restore(&mut mv);
            assert_eq_api!(mv, v => v.extend_from_slice(&v.clone()));
            restore(&mut mv);
            assert_eq_api!(mv, v => v.into_iter().collect::<TheVec<_>>().into_std());

            restore(&mut mv);
            assert_eq_api!(mv, v => v.retain(|value| value % 3 == 0 || value % 4 == 0));

            restore(&mut mv);
            assert_eq_api!(mv, v => v.retain_mut(|value| {
                *value += 1;
                *value % 3 == 0 || *value % 4 == 0
            }));

            restore(&mut mv);
            assert_eq_api!(mv, v => v.dedup());

            restore(&mut mv);
            assert_eq_api!(mv, v => v.dedup_by(|lhs, rhs| lhs < rhs));

            restore(&mut mv);
            assert_eq_api!(mv, v => v.dedup_by_key(|value| *value % 3));

            for i in 0..v.len() {
                restore(&mut mv);
                assert_eq_api!(mv, v => v.swap_remove(i.into_tic()));
                restore(&mut mv);
                assert_eq_api!(mv, v => v.insert(i.into_tic(), 123));
                restore(&mut mv);
                assert_eq_api!(mv, v => v.remove(i.into_tic()));
                restore(&mut mv);
                unsafe { assert_eq_api!(mv, v => v.set_len(i)) };
                restore(&mut mv);
                assert_eq_api!(mv, v => v.split_off(i.into_tic()).into_std());
            }

            for a in 0..v.len() {
                for b in a..v.len() {
                    restore(&mut mv);
                    assert_eq_api!(mv, v => v.drain((a..b).into_tic()).collect::<Vec<_>>());
                    restore(&mut mv);
                    assert_eq_api!(mv, v => v.extend_from_within((a..b).into_tic()));
                    restore(&mut mv);
                    assert_eq_api!(
                        mv, v => v.splice((a..b).into_tic(), [1, 2, 3]).collect::<Vec<_>>()
                    );
                }
            }
            restore(&mut mv);
            assert_eq_api!(mv, v => v.splice(.., [1, 2, 3]).collect::<Vec<_>>());

            restore(&mut mv);
            assert_eq_api!(mv, v => v.clear());
        }
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_vec_hash_compatibility() {
        for v in [
            &[0_u32; 0][..],
            &[1],
            &[1, 1234],
            &[1, 2, 4],
            &[1, 5, 3, 2],
            &[1, 1, 9, 2, 4, 1, 12345, 12],
        ] {
            let cv = (v.to_vec(), TiVec::<Id, _>::from(v.to_vec()));
            let mut cv = (&cv.0, &cv.1);
            assert_eq_api!(cv, v => {
                let mut hasher = DefaultHasher::new();
                v.hash(&mut hasher);
                hasher.finish()
            });
        }
    }

    #[test]
    fn test_u8_vec_api_compatibility() {
        assert_eq!(
            Vec::from(TiVec::<Id, u8>::from("abc")),
            Vec::<u8>::from("abc"),
        );
        assert_eq!(
            Vec::from(TiVec::<Id, u8>::from("abc".to_owned())),
            Vec::<u8>::from("abc".to_owned()),
        );
        assert_eq!(
            Vec::from(TiVec::<Id, u8>::from(CString::new("abc").unwrap())),
            Vec::<u8>::from(CString::new("abc").unwrap()),
        );

        for v in [&b"abc"[..], b"aBc", b"ABC", b"abd", b"a\x80\x81b"] {
            let cv = (v.to_vec(), TiVec::<Id, _>::from(v.to_vec()));
            let mut cv = (&cv.0, &cv.1);

            assert_eq_api!(cv, v => TheVec::from(v.as_slice()).into_std());
        }
    }

    #[test]
    fn test_vec_debug() {
        let s0: TiVec<Id, u32> = TiVec::from(alloc::vec![]);
        let s1: TiVec<Id, u32> = TiVec::from(alloc::vec![12]);
        let s2: TiVec<Id, u32> = TiVec::from(alloc::vec![23, 34]);
        assert_eq!(&alloc::format!("{s0:?}"), "{}");
        assert_eq!(&alloc::format!("{s1:?}"), "{Id(0): 12}");
        assert_eq!(&alloc::format!("{s2:?}"), "{Id(0): 23, Id(1): 34}");
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_vec_write() {
        let mut mv = (Vec::<u8>::new(), TiVec::<Id, u8>::new());
        let mut mv = (&mut mv.0, &mut mv.1);

        assert_eq_api!(mv, v => v.write(&[1, 2, 3]).unwrap());
        assert_eq_api!(mv, v => v.write_vectored(
            &[IoSlice::new(&[1, 2, 3]), IoSlice::new(&[4, 5])]
        ).unwrap());
        assert_eq_api!(mv, v => v.write_all(&[1, 2, 3]).unwrap());
        assert_eq_api!(mv, v => v.flush().unwrap());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_vec_serialize() {
        let s0: TiVec<Id, u32> = TiVec::from(alloc::vec![]);
        let s1: TiVec<Id, u32> = TiVec::from(alloc::vec![12]);
        let s2: TiVec<Id, u32> = TiVec::from(alloc::vec![23, 34]);
        assert_eq!(&serde_json::to_string(&s0).unwrap(), "[]");
        assert_eq!(&serde_json::to_string(&s1).unwrap(), "[12]");
        assert_eq!(&serde_json::to_string(&s2).unwrap(), "[23,34]");
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_vec_deserialize() {
        let s0: TiVec<Id, u32> = serde_json::from_str("[]").unwrap();
        let s1: TiVec<Id, u32> = serde_json::from_str("[12]").unwrap();
        let s2: TiVec<Id, u32> = serde_json::from_str("[23, 34]").unwrap();
        assert_eq!(s0.as_slice().raw, [0; 0][..]);
        assert_eq!(s1.as_slice().raw, [12][..]);
        assert_eq!(s2.as_slice().raw, [23, 34][..]);
    }

    #[cfg(feature = "bincode")]
    #[test]
    fn test_vec_encode() {
        let config = bincode::config::standard();
        let s0: TiVec<Id, u32> = TiVec::from(alloc::vec![]);
        let s1: TiVec<Id, u32> = TiVec::from(alloc::vec![12]);
        let s2: TiVec<Id, u32> = TiVec::from(alloc::vec![23, 34]);
        let s3: TiVec<Id, u32> = TiVec::from(alloc::vec![0x1234_5678, 0x2345_6789]);
        assert_eq!(&bincode::encode_to_vec(s0, config).unwrap(), &[0]);
        assert_eq!(&bincode::encode_to_vec(s1, config).unwrap(), &[1, 12]);
        assert_eq!(&bincode::encode_to_vec(s2, config).unwrap(), &[2, 23, 34]);
        assert_eq!(
            &bincode::encode_to_vec(s3, config).unwrap(),
            &[2, 252, 0x78, 0x56, 0x34, 0x12, 252, 0x89, 0x67, 0x45, 0x23]
        );
    }

    #[cfg(feature = "bincode")]
    #[test]
    fn test_vec_decode() {
        fn decode_whole(bytes: &[u8]) -> TiVec<Id, u32> {
            let config = bincode::config::standard();
            let (decoded, len) = bincode::decode_from_slice(bytes, config).unwrap();
            assert_eq!(len, bytes.len());
            decoded
        }

        let s0: TiVec<Id, u32> = decode_whole(&[0]);
        let s1: TiVec<Id, u32> = decode_whole(&[1, 12]);
        let s2: TiVec<Id, u32> = decode_whole(&[2, 23, 34]);
        let s3: TiVec<Id, u32> =
            decode_whole(&[2, 252, 0x78, 0x56, 0x34, 0x12, 252, 0x89, 0x67, 0x45, 0x23]);
        assert_eq!(s0.as_slice().raw, [0; 0][..]);
        assert_eq!(s1.as_slice().raw, [12][..]);
        assert_eq!(s2.as_slice().raw, [23, 34][..]);
        assert_eq!(s3.as_slice().raw, [0x1234_5678, 0x2345_6789][..]);
    }

    #[cfg(feature = "bincode")]
    #[test]
    fn test_boxed_slice_borrow_decode() {
        fn decode_whole(bytes: &[u8]) -> TiVec<Id, &str> {
            let config = bincode::config::standard();
            let (decoded, len) = bincode::borrow_decode_from_slice(bytes, config).unwrap();
            assert_eq!(len, bytes.len());
            decoded
        }

        let s0: TiVec<Id, &str> = decode_whole(&[0]);
        let s1: TiVec<Id, &str> = decode_whole(&[1, 1, b'a']);
        let s2: TiVec<Id, &str> = decode_whole(&[2, 2, b'b', b'c', 3, b'd', b'e', b'f']);
        assert_eq!(s0.as_slice().raw, [""; 0][..]);
        assert_eq!(s1.as_slice().raw, ["a"][..]);
        assert_eq!(s2.as_slice().raw, ["bc", "def"][..]);
    }

    #[rustversion::since(1.100.0)]
    #[cfg(feature = "nightly")]
    #[test]
    fn test_allocator_api() {
        use alloc::alloc::Global;
        use core::alloc::{AllocError, Allocator, Layout};
        use core::ptr::NonNull;
        use core::sync::atomic::{AtomicUsize, Ordering};

        #[derive(Default)]
        struct TrackingAllocator {
            allocs: AtomicUsize,
            deallocs: AtomicUsize,
        }

        impl TrackingAllocator {
            fn allocs(&self) -> usize {
                self.allocs.load(Ordering::Relaxed)
            }

            fn deallocs(&self) -> usize {
                self.deallocs.load(Ordering::Relaxed)
            }
        }

        unsafe impl Allocator for TrackingAllocator {
            fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
                let _ = self.allocs.fetch_add(1, Ordering::Relaxed);
                Global.allocate(layout)
            }

            unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
                let _ = self.deallocs.fetch_add(1, Ordering::Relaxed);
                unsafe { Global.deallocate(ptr, layout) }
            }
        }

        let alloc = TrackingAllocator::default();
        let is_our_alloc = |a: &&TrackingAllocator| core::ptr::eq(*a, &raw const alloc);

        let vec1: Vec<i32, _> = Vec::new_in(&alloc);
        #[expect(clippy::assert_is_empty, reason = "simpler check")]
        (assert!(vec1.is_empty()));
        assert!(is_our_alloc(vec1.allocator()));
        assert_eq!(alloc.allocs(), 0);
        assert_eq!(alloc.deallocs(), 0);

        let mut vec2: Vec<i32, _> = Vec::with_capacity_in(4, &alloc);
        assert!(vec2.capacity() >= 4);
        assert!(is_our_alloc(vec2.allocator()));
        assert_eq!(alloc.allocs(), 1);
        assert_eq!(alloc.deallocs(), 0);

        vec2.extend_from_slice(&[1, 2, 3, 4]);
        assert_eq!(&vec2[..], &[1, 2, 3, 4]);
        assert_eq!(alloc.allocs(), 1);
        assert_eq!(alloc.deallocs(), 0);

        let slice: &[i32] = &[5, 6, 7];
        let vec3 = slice.to_vec_in(&alloc);
        assert!(is_our_alloc(vec3.allocator()));
        assert_eq!(&vec3[..], &[5, 6, 7]);
        assert_eq!(alloc.allocs(), 2);
        assert_eq!(alloc.deallocs(), 0);

        let (ptr, len, cap, alloc_ref) = vec2.into_raw_parts_with_allocator();
        assert_eq!(len, 4);
        assert!(cap >= 4);
        assert!(is_our_alloc(&alloc_ref));
        assert_eq!(alloc.allocs(), 2);
        assert_eq!(alloc.deallocs(), 0);

        let vec2: Vec<i32, _> = unsafe { Vec::from_raw_parts_in(ptr, len, cap, alloc_ref) };
        assert_eq!(&vec2[..], &[1, 2, 3, 4]);
        assert!(is_our_alloc(&alloc_ref));
        assert_eq!(alloc.allocs(), 2);
        assert_eq!(alloc.deallocs(), 0);

        drop(vec1);
        assert_eq!(alloc.allocs(), 2);
        assert_eq!(alloc.deallocs(), 0);

        drop(vec2);
        assert_eq!(alloc.allocs(), 2);
        assert_eq!(alloc.deallocs(), 1);

        drop(vec3);
        assert_eq!(alloc.allocs(), 2);
        assert_eq!(alloc.deallocs(), 2);
    }
}
