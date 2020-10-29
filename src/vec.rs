use core::{
    borrow::{Borrow, BorrowMut},
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    iter::FromIterator,
    marker::PhantomData,
    ops,
    slice::{self /*SliceIndex*/},
};

use alloc::{
    boxed::Box,
    vec::{self, Drain, Splice, Vec},
};

#[cfg(feature = "serde")]
use serde::ser::{Serialize, Serializer};

#[cfg(any(feature = "serde-alloc", feature = "serde-std"))]
use serde::de::{Deserialize, Deserializer};

use crate::{TiEnumerated, TiRangeBounds, TiSlice};

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
/// `TiVec<K, V>` can be converted to [`std::vec::Vec<V>`][`std::vec::Vec`] and back
/// using [`From`] and [`Into`].
///
/// There are also zero-cost conversions available between references:
/// - [`&std::vec::Vec<V>`][`std::vec::Vec`] and `&TiVec<K, V>` with [`AsRef`],
/// - [`&mut std::vec::Vec<V>`][`std::vec::Vec`] and `&mut TiVec<K, V>` with [`AsMut`],
///
/// Added methods:
/// - [`from_ref`] - Converts a [`&std::vec::Vec<V>`][`std::vec::Vec`]
///   into a `&TiVec<K, V>`.
/// - [`from_mut`] - Converts a [`&mut std::vec::Vec<V>`][`std::vec::Vec`]
///   into a `&mut TiVec<K, V>`.
/// - [`push_and_get_key`] - Appends an element to the back of a collection
///   and returns its index of type `K`.
/// - [`pop_key_value`] - Removes the last element from a vector and returns it
///   with its index of type `K`, or [`None`] if the vector is empty.
/// - [`drain_enumerated`] - Creates a draining iterator that removes the specified
///   range in the vector and yields the current count and the removed items.
///   It acts like `self.drain(range).enumerate()`,
///   but instead of `usize` it returns index of type `K`.
/// - [`into_iter_enumerated`] - Converts the vector into iterator over all key-value pairs
///   with `K` used for iteration indices.
///   It acts like `self.into_iter().enumerate()`,
///   but use `K` instead of `usize` for iteration indices.
///
/// # Example
///
/// ```
/// use typed_index_collections::TiVec;
/// use derive_more::{From, Into};
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
/// [`drain_enumerated`]: #method.drain_enumerated
/// [`into_iter_enumerated`]: #method.into_iter_enumerated
/// [`std::vec::Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
/// [`From`]: https://doc.rust-lang.org/std/convert/trait.From.html
/// [`Into`]: https://doc.rust-lang.org/std/convert/trait.Into.html
/// [`AsRef`]: https://doc.rust-lang.org/std/convert/trait.AsRef.html
/// [`AsMut`]: https://doc.rust-lang.org/std/convert/trait.AsMut.html
/// [`derive_more`]: https://crates.io/crates/derive_more
pub struct TiVec<K, V> {
    /// Raw slice property
    pub raw: Vec<V>,

    /// Tied slice index type
    ///
    /// `fn(T) -> T` is *[PhantomData pattern][phantomdata patterns]*
    /// used to relax auto trait implementations bounds for
    /// [`Send`], [`Sync`], [`Unpin`], [`UnwindSafe`] and [`RefUnwindSafe`].
    ///
    /// Derive attribute is not used for trait implementations because it also requires
    /// the same trait implemented for K that is an unnecessary requirement.
    ///
    /// [phantomdata patterns]: https://doc.rust-lang.org/nomicon/phantom-data.html#table-of-phantomdata-patterns
    /// [`Send`]: https://doc.rust-lang.org/core/marker/trait.Send.html
    /// [`Sync`]: https://doc.rust-lang.org/core/marker/trait.Sync.html
    /// [`Unpin`]: https://doc.rust-lang.org/core/marker/trait.Unpin.html
    /// [`UnwindSafe`]: https://doc.rust-lang.org/core/std/panic/trait.UnwindSafe.html
    /// [`RefUnwindSafe`]: https://doc.rust-lang.org/core/std/panic/trait.RefUnwindSafe.html
    _marker: PhantomData<fn(K) -> K>,
}

impl<K, V> TiVec<K, V> {
    /// Constructs a new, empty `TiVec<K, V>`.
    ///
    /// See [`Vec::new`] for more details.
    ///
    /// [`Vec::new`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.new
    #[inline]
    pub fn new() -> Self {
        Self {
            raw: Vec::new(),
            _marker: PhantomData,
        }
    }

    /// Constructs a new, empty `TiVec<K, V>` with the specified capacity.
    ///
    /// See [`Vec::with_capacity`] for more details.
    ///
    /// [`Vec::with_capacity`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.with_capacity
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            raw: Vec::with_capacity(capacity),
            _marker: PhantomData,
        }
    }

    /// Creates a `TiVec<K, V>` directly from the raw components of another vector.
    ///
    /// See [`Vec::from_raw_parts`] for more details.
    ///
    /// [`Vec::from_raw_parts`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.from_raw_parts
    #[allow(clippy::missing_safety_doc)]
    pub unsafe fn from_raw_parts(ptr: *mut V, length: usize, capacity: usize) -> Self {
        Self {
            raw: Vec::from_raw_parts(ptr, length, capacity),
            _marker: PhantomData,
        }
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
    #[allow(trivial_casts, clippy::ptr_arg)]
    #[inline]
    pub fn from_ref(raw: &Vec<V>) -> &Self {
        unsafe { &*(raw as *const Vec<V> as *const Self) }
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
    /// [`&std::vec::mut Vec<V>`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
    #[allow(trivial_casts)]
    #[inline]
    pub fn from_mut(raw: &mut Vec<V>) -> &mut Self {
        unsafe { &mut *(raw as *mut Vec<V> as *mut Self) }
    }

    /// Returns the number of elements the vector can hold without
    /// reallocating.
    ///
    /// See [`Vec::capacity`] for more details.
    ///
    /// [`Vec::capacity`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.capacity
    #[inline]
    pub fn capacity(&self) -> usize {
        self.raw.capacity()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `TiVec<K, V>`. The collection may reserve more space to avoid
    /// frequent reallocations. After calling `reserve`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// See [`Vec::reserve`] for more details.
    ///
    /// [`Vec::reserve`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.reserve
    pub fn reserve(&mut self, additional: usize) {
        self.raw.reserve(additional)
    }

    /// Reserves the minimum capacity for exactly `additional` more elements to
    /// be inserted in the given `TiVec<K, V>`. After calling `reserve_exact`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// See [`Vec::reserve_exact`] for more details.
    ///
    /// [`Vec::reserve_exact`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.reserve_exact
    pub fn reserve_exact(&mut self, additional: usize) {
        self.raw.reserve_exact(additional)
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// See [`Vec::shrink_to_fit`] for more details.
    ///
    /// [`Vec::shrink_to_fit`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.shrink_to_fit
    pub fn shrink_to_fit(&mut self) {
        self.raw.shrink_to_fit()
    }

    /// Converts the vector into [`Box<TiSlice<K, V>>`][`Box`].
    ///
    /// See [`Vec::into_boxed_slice`] for more details.
    ///
    /// [`Vec::into_boxed_slice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.into_boxed_slice
    /// [`Box`]: https://doc.rust-lang.org/std/boxed/struct.Box.html
    pub fn into_boxed_slice(self) -> Box<TiSlice<K, V>> {
        self.raw.into_boxed_slice().into()
    }

    /// Shortens the vector, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// See [`Vec::truncate`] for more details.
    ///
    /// [`Vec::truncate`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.truncate
    pub fn truncate(&mut self, len: usize) {
        self.raw.truncate(len)
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// See [`Vec::as_slice`] for more details.
    ///
    /// [`Vec::as_slice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_slice
    #[inline]
    pub fn as_slice(&self) -> &TiSlice<K, V> {
        self.raw.as_slice().as_ref()
    }

    /// Extracts a mutable slice of the entire vector.
    ///
    /// See [`Vec::as_mut_slice`] for more details.
    ///
    /// [`Vec::as_mut_slice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_mut_slice
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut TiSlice<K, V> {
        self.raw.as_mut_slice().as_mut()
    }

    /// Returns a raw pointer to the vector's buffer.
    ///
    /// See [`Vec::as_ptr`] for more details.
    ///
    /// [`Vec::as_ptr`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_ptr
    #[inline]
    pub fn as_ptr(&self) -> *const V {
        self.raw.as_ptr()
    }

    /// Returns an unsafe mutable pointer to the vector's buffer.
    ///
    /// See [`Vec::as_mut_ptr`] for more details.
    ///
    /// [`Vec::as_mut_ptr`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.as_mut_ptr
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut V {
        self.raw.as_mut_ptr()
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// See [`Vec::set_len`] for more details.
    ///
    /// [`Vec::set_len`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.set_len
    #[allow(clippy::missing_safety_doc)]
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        self.raw.set_len(new_len)
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
        usize: From<K>,
    {
        self.raw.swap_remove(index.into())
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// See [`Vec::insert`] for more details.
    ///
    /// [`Vec::insert`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.insert
    pub fn insert(&mut self, index: K, element: V)
    where
        usize: From<K>,
    {
        self.raw.insert(index.into(), element)
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// See [`Vec::remove`] for more details.
    ///
    /// [`Vec::remove`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.remove
    pub fn remove(&mut self, index: K) -> V
    where
        usize: From<K>,
    {
        self.raw.remove(index.into())
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// See [`Vec::retain`] for more details.
    ///
    /// [`Vec::retain`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.retain
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&V) -> bool,
    {
        self.raw.retain(f)
    }

    /// Removes all but the first of consecutive elements in the vector that resolve to the same
    /// key.
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
        self.raw.dedup_by_key(key)
    }

    /// Removes all but the first of consecutive elements in the vector satisfying a given equality
    /// relation.
    ///
    /// See [`Vec::dedup_by`] for more details.
    ///
    /// [`Vec::dedup_by`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.dedup_by
    pub fn dedup_by<F>(&mut self, same_bucket: F)
    where
        F: FnMut(&mut V, &mut V) -> bool,
    {
        self.raw.dedup_by(same_bucket)
    }

    /// Appends an element to the back of a collection.
    ///
    /// See [`Vec::push`] for more details.
    ///
    /// [`Vec::push`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.push
    #[inline]
    pub fn push(&mut self, value: V) {
        self.raw.push(value)
    }

    /// Appends an element to the back of a collection and returns its index of type `K`.
    ///
    /// Using of `{ vec.push(...); vec.last_key().unwrap() }` is not recommended,
    /// because it is not well optimized and generates an unreachable panic call.
    /// This function uses [`slice::next_key`] instead.
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
        K: From<usize>,
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
    /// [`Vec::pop`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.pop
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
    /// [`Vec::push`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.push
    #[inline]
    pub fn pop_key_value(&mut self) -> Option<(K, V)>
    where
        K: From<usize>,
    {
        self.raw.pop().map(|value| (self.raw.len().into(), value))
    }

    /// Moves all the elements of `other` into `Self`, leaving `other` empty.
    ///
    /// See [`Vec::append`] for more details.
    ///
    /// [`Vec::append`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.append
    #[inline]
    pub fn append(&mut self, other: &mut Self) {
        self.raw.append(&mut other.raw)
    }

    /// Creates a draining iterator that removes the specified range in the vector
    /// and yields the removed items.
    ///
    /// See [`Vec::drain`] for more details.
    ///
    /// [`Vec::drain`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.drain
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
    #[inline]
    pub fn drain_enumerated<R>(&mut self, range: R) -> TiEnumerated<Drain<'_, V>, K, V>
    where
        K: From<usize>,
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
        self.raw.clear()
    }

    /// Returns the number of elements in the vector, also referred to
    /// as its 'length'.
    ///
    /// See [`Vec::len`] for more details.
    ///
    /// [`Vec::len`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.len
    #[inline]
    pub fn len(&self) -> usize {
        self.raw.len()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// See [`Vec::is_empty`] for more details.
    ///
    /// [`Vec::is_empty`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.is_empty
    pub fn is_empty(&self) -> bool {
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
        usize: From<K>,
    {
        self.raw.split_off(at.into()).into()
    }

    /// Resizes the `TiVec` in-place so that `len` is equal to `new_len`.
    ///
    /// See [`Vec::resize_with`] for more details.
    ///
    /// [`Vec::resize_with`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.resize_with
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> V,
    {
        self.raw.resize_with(new_len, f)
    }

    /// Resizes the `TiVec` in-place so that `len` is equal to `new_len`.
    ///
    /// See [`Vec::resize`] for more details.
    ///
    /// [`Vec::resize`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.resize
    pub fn resize(&mut self, new_len: usize, value: V)
    where
        V: Clone,
    {
        self.raw.resize(new_len, value)
    }

    /// Clones and appends all elements in a slice to the `TiVec`.
    ///
    /// See [`Vec::extend_from_slice`] for more details.
    ///
    /// [`Vec::extend_from_slice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.extend_from_slice
    pub fn extend_from_slice(&mut self, other: &TiSlice<K, V>)
    where
        V: Clone,
    {
        self.raw.extend_from_slice(&other.raw)
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
        self.raw.dedup()
    }

    /// Creates a splicing iterator that replaces the specified range in the vector
    /// with the given `replace_with` iterator and yields the removed items.
    /// `replace_with` does not need to be the same length as `range`.
    ///
    /// See [`Vec::splice`] for more details.
    ///
    /// [`Vec::splice`]: https://doc.rust-lang.org/std/vec/struct.Vec.html#method.splice
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
    #[inline(always)]
    pub fn into_iter_enumerated(self) -> TiEnumerated<vec::IntoIter<V>, K, V>
    where
        K: From<usize>,
    {
        self.raw
            .into_iter()
            .enumerate()
            .map(|(key, value)| (key.into(), value))
    }
}

impl<K, V> fmt::Debug for TiVec<K, V>
where
    K: fmt::Debug + From<usize>,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter_enumerated()).finish()
    }
}

impl<K, V> AsRef<TiVec<K, V>> for TiVec<K, V> {
    fn as_ref(&self) -> &TiVec<K, V> {
        self
    }
}

impl<K, V> AsMut<TiVec<K, V>> for TiVec<K, V> {
    fn as_mut(&mut self) -> &mut TiVec<K, V> {
        self
    }
}

impl<K, V> AsRef<TiSlice<K, V>> for TiVec<K, V> {
    fn as_ref(&self) -> &TiSlice<K, V> {
        self
    }
}

impl<K, V> AsMut<TiSlice<K, V>> for TiVec<K, V> {
    fn as_mut(&mut self) -> &mut TiSlice<K, V> {
        self
    }
}

impl<K, V> AsRef<Vec<V>> for TiVec<K, V> {
    fn as_ref(&self) -> &Vec<V> {
        &self.raw
    }
}

impl<K, V> AsMut<Vec<V>> for TiVec<K, V> {
    fn as_mut(&mut self) -> &mut Vec<V> {
        &mut self.raw
    }
}

impl<K, V> AsRef<[V]> for TiVec<K, V> {
    fn as_ref(&self) -> &[V] {
        &self.raw
    }
}

impl<K, V> AsMut<[V]> for TiVec<K, V> {
    fn as_mut(&mut self) -> &mut [V] {
        &mut self.raw
    }
}

impl<K, V> AsRef<TiVec<K, V>> for Vec<V> {
    fn as_ref(&self) -> &TiVec<K, V> {
        TiVec::from_ref(self)
    }
}

impl<K, V> AsMut<TiVec<K, V>> for Vec<V> {
    fn as_mut(&mut self) -> &mut TiVec<K, V> {
        TiVec::from_mut(self)
    }
}

impl<K, V> Borrow<TiSlice<K, V>> for TiVec<K, V> {
    fn borrow(&self) -> &TiSlice<K, V> {
        self.as_slice()
    }
}

impl<K, V> BorrowMut<TiSlice<K, V>> for TiVec<K, V> {
    fn borrow_mut(&mut self) -> &mut TiSlice<K, V> {
        self.as_mut_slice()
    }
}

impl<K, V> ops::Deref for TiVec<K, V> {
    type Target = TiSlice<K, V>;

    fn deref(&self) -> &TiSlice<K, V> {
        Self::Target::from_ref(&self.raw)
    }
}

impl<K, V> ops::DerefMut for TiVec<K, V> {
    fn deref_mut(&mut self) -> &mut TiSlice<K, V> {
        Self::Target::from_mut(&mut self.raw)
    }
}

impl<K, V> FromIterator<V> for TiVec<K, V> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        Self {
            raw: Vec::from_iter(iter),
            _marker: PhantomData,
        }
    }
}

impl<K, A, B> PartialEq<TiVec<K, B>> for TiVec<K, A>
where
    A: PartialEq<B>,
{
    #[inline]
    fn eq(&self, other: &TiVec<K, B>) -> bool {
        self.raw == other.raw
    }
}

impl<'a, K, A, B> PartialEq<&'a TiSlice<K, B>> for TiVec<K, A>
where
    A: PartialEq<B>,
{
    #[inline]
    fn eq(&self, other: &&'a TiSlice<K, B>) -> bool {
        *self.raw == other.raw
    }
}

impl<'a, K, A, B> PartialEq<&'a mut TiSlice<K, B>> for TiVec<K, A>
where
    A: PartialEq<B>,
{
    #[inline]
    fn eq(&self, other: &&'a mut TiSlice<K, B>) -> bool {
        *self.raw == other.raw
    }
}

impl<K, V> PartialOrd<TiVec<K, V>> for TiVec<K, V>
where
    V: PartialOrd<V>,
{
    #[inline]
    fn partial_cmp(&self, other: &TiVec<K, V>) -> Option<Ordering> {
        self.raw.partial_cmp(&other.raw)
    }
}

impl<K, V> Clone for TiVec<K, V>
where
    V: Clone,
{
    #[inline]
    fn clone(&self) -> TiVec<K, V> {
        self.raw.clone().into()
    }
}

impl<K, V> Default for TiVec<K, V> {
    #[inline]
    fn default() -> Self {
        Vec::default().into()
    }
}

impl<K, V> Eq for TiVec<K, V> where V: Eq {}

impl<K, V> Hash for TiVec<K, V>
where
    V: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state)
    }
}

impl<K, V> Ord for TiVec<K, V>
where
    V: Ord,
{
    #[inline]
    fn cmp(&self, other: &TiVec<K, V>) -> Ordering {
        self.raw.cmp(&other.raw)
    }
}

impl<K, V> From<Vec<V>> for TiVec<K, V> {
    fn from(vec: Vec<V>) -> Self {
        Self {
            raw: vec,
            _marker: PhantomData,
        }
    }
}

impl<K, V> From<TiVec<K, V>> for Vec<V> {
    fn from(vec: TiVec<K, V>) -> Self {
        vec.raw
    }
}

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

#[cfg(feature = "serde")]
impl<K, V: Serialize> Serialize for TiVec<K, V> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.raw.as_slice().serialize(serializer)
    }
}

#[cfg(any(feature = "serde-alloc", feature = "serde-std"))]
impl<'de, K, V: Deserialize<'de>> Deserialize<'de> for TiVec<K, V> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Vec::deserialize(deserializer).map(Into::into)
    }
}

#[cfg(test)]
mod test {
    use crate::test::Id;

    trait VecWithCapacity
    where
        Self: Sized,
    {
        fn and_capacity(self) -> (usize, Self);
    }

    impl<T> VecWithCapacity for alloc::vec::Vec<T> {
        fn and_capacity(self) -> (usize, Self) {
            (self.capacity(), self)
        }
    }

    macro_rules! assert_eq_vec_api {
        ($source:expr => |&$arg:ident| $expr:expr) => {
            assert_eq_api!($source.clone() => |$arg| {
                let $arg = $arg.into_t();
                let value = $expr;
                (value, $arg.into_t().and_capacity())
            });
        };
        ($source:expr => |&mut $arg:ident| $expr:expr) => {
            assert_eq_api!($source.clone() => |$arg| {
                let mut $arg = $arg.into_t();
                let value = $expr;
                (value, $arg.into_t().and_capacity())
            });
        };
    }

    #[test]
    fn api_compatibility() {
        use crate::TiVec;
        use alloc::vec;
        use alloc::vec::Vec;

        assert_eq_api!(UsizeVec::new().into_t().and_capacity());
        for &j in &[0, 1, 2, 4] {
            assert_eq_api!(UsizeVec::with_capacity(j).into_t().and_capacity());
        }
        for vec in &[
            vec![0; 0],
            vec![1],
            vec![1, 2],
            vec![1, 2, 4],
            vec![1, 2, 4, 8],
            vec![1, 3],
            vec![7, 3, 5],
            vec![10, 6, 35, 4],
            vec![1, 3, 3, 2, 4, 4, 4],
        ] {
            assert_eq_api!(vec.clone() => |vec| {
                let mut vec = core::mem::ManuallyDrop::new(vec);
                unsafe {
                    UsizeVec::from_raw_parts(vec.as_mut_ptr(), vec.len(), vec.capacity())
                }.into_t()
            });
            assert_eq_api!(vec.clone() => |vec| vec.into_t().capacity());
            for j in 0..8 {
                assert_eq_vec_api!(vec => |&mut vec| vec.reserve(j));
                assert_eq_vec_api!(vec => |&mut vec| vec.reserve_exact(j));
                assert_eq_vec_api!(vec => |&mut vec| {
                    vec.reserve(j);
                    vec.shrink_to_fit();
                });
            }
            assert_eq_api!(vec.clone() => |vec| vec.into_t().into_boxed_slice().into_t());
            for j in 0..8 {
                assert_eq_vec_api!(vec => |&mut vec| vec.truncate(j));
            }
            assert_eq_api!(vec.clone() => |vec| vec.into_t().as_slice().into_t());
            assert_eq_api!(vec.clone() => |vec| vec.into_t().as_mut_slice().into_t());
            assert_eq_api!(&vec => |vec| vec.into_t().as_ptr());
            {
                let mut vec = vec.clone();
                let vec_ref_mut = &mut vec;
                let vec_ptr_mut = vec_ref_mut.as_mut_ptr();
                let ti_vec_ref_mut: &mut TiVec<Id, _> = vec_ref_mut.as_mut();
                let ti_vec_ptr_mut = ti_vec_ref_mut.as_mut_ptr();
                assert_eq!(vec_ptr_mut, ti_vec_ptr_mut);
            }
            assert_eq_api!(vec.clone() => |vec| {
                const NUM_ADDED_ITEMS: usize = 4;
                let mut vec = vec.into_t();
                let initial_len = vec.len();
                vec.reserve(NUM_ADDED_ITEMS);
                unsafe {
                    for j in 0..NUM_ADDED_ITEMS {
                        *vec.as_mut_slice().into_t().get_unchecked_mut(initial_len + j) = j;
                    }
                    vec.set_len(initial_len + NUM_ADDED_ITEMS);
                }
                vec.into_t().and_capacity()
            });
            for j in 0..vec.len() {
                assert_eq_vec_api!(vec => |&mut vec| vec.swap_remove(j.into_t()));
                assert_eq_vec_api!(vec => |&mut vec| vec.insert(j.into_t(), 123));
                assert_eq_vec_api!(vec => |&mut vec| vec.remove(j.into_t()));
            }
            assert_eq_vec_api!(vec => |&mut vec|
                vec.retain(|value| value % 3 == 0 || value % 4 == 0));
            assert_eq_vec_api!(vec => |&mut vec|
                vec.dedup_by_key(|value| *value % 3 == 0 || *value % 4 == 0));
            assert_eq_vec_api!(vec => |&mut vec| vec.dedup_by(|lhs, rhs| lhs < rhs));
            assert_eq_vec_api!(vec => |&mut vec| vec.push(123));
            assert_eq_vec_api!(vec => |&mut vec| vec.pop());
            for other_vec in &[
                vec![0; 0],
                vec![1],
                vec![1, 2],
                vec![1, 2, 4],
                vec![1, 2, 4, 8],
                vec![1, 3],
                vec![7, 3, 5],
                vec![10, 6, 35, 4],
            ] {
                assert_eq_api!({
                    let mut vec = vec.clone().into_t();
                    let mut other_vec = other_vec.clone().into_t();
                    vec.append(&mut other_vec);
                    vec.into_t().and_capacity()
                });
            }
            for start in 0..vec.len() {
                for end in start..vec.len() {
                    assert_eq_vec_api!(vec => |&mut vec| {
                        let iter = vec.drain(start.into_t()..end.into_t());
                        let vec: Vec<_> = iter.collect();
                        vec
                    });
                }
            }

            assert_eq_vec_api!(vec => |&mut vec| vec.clear());
            assert_eq_vec_api!(vec => |&vec| vec.len());
            assert_eq_vec_api!(vec => |&vec| vec.is_empty());
            for j in 0..vec.len() {
                assert_eq_vec_api!(vec => |&mut vec| vec.split_off(j.into_t()).into_t());
            }
            for j in 0..8 {
                assert_eq_vec_api!(vec => |&mut vec| {
                    let mut items = 0..;
                    vec.resize_with(j, || items.next().unwrap())
                });
                assert_eq_vec_api!(vec => |&mut vec| vec.resize(j, 123));
            }
            for slice in &[
                &[0; 0][..],
                &[1],
                &[1, 2],
                &[1, 2, 4],
                &[1, 2, 4, 8],
                &[1, 3],
                &[7, 3, 5],
                &[10, 6, 35, 4],
            ] {
                assert_eq_vec_api!(vec => |&mut vec| vec.extend_from_slice(slice.into_t()));
            }
            assert_eq_vec_api!(vec => |&mut vec| vec.dedup());
            for start in 0..vec.len() {
                for end in start..vec.len() {
                    assert_eq_vec_api!(vec => |&mut vec| {
                        let iter = vec.splice(start.into_t()..end.into_t(), 10..20);
                        let vec: Vec<_> = iter.collect();
                        vec
                    });
                }
            }
        }
    }
}
