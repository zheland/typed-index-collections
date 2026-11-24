#[cfg(feature = "alloc")]
mod boxed;

#[cfg(feature = "alloc")]
use core::alloc::Allocator;
use core::borrow::{Borrow, BorrowMut};
use core::cell::Cell;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem::{transmute_copy, ManuallyDrop, MaybeUninit};
use core::ops::{Index, IndexMut};
use core::{array, fmt, ptr, slice};

#[cfg(feature = "alloc")]
use alloc::boxed::Box;
#[cfg(feature = "bincode")]
use bincode::de::{BorrowDecoder, Decoder};
#[cfg(feature = "bincode")]
use bincode::enc::Encoder;
#[cfg(feature = "bincode")]
use bincode::error::{DecodeError, EncodeError};
#[cfg(feature = "bincode")]
use bincode::{BorrowDecode, Decode, Encode};
#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{TiEnumerated, TiSlice};

/// A fixed-size array that only accepts keys of the type `K`.
///
/// `TiArray<K, V, N>` is a wrapper around Rust [`array`] type.
/// The struct mirrors the stable API of Rust [`array`]
/// and forwards to it as much as possible.
///
/// `TiArray<K, V, N>` uses `K` instead of `usize` for element indices and
/// require the index to implement
/// [`From<usize>`][`From`] and [`Into<usize>`][`Into`] traits.
/// Their implementation can be easily done
/// with [`derive_more`] crate and `#[derive(From, Into)]`.
///
/// `TiArray<K, V, N>` can be converted to [`[V; N]`][`array`] and
/// back using [`From`] and [`Into`].
///
/// There are also zero-cost conversions available between references:
/// - [`&[V; N]`][`array`] and `&TiArray<K, V, N>` with [`AsRef`],
/// - [`&mut [V; N]`][`array`] and `&mut TiArray<K, V, N>` with
///   [`AsMut`],
///
/// Added methods:
/// - [`from_ref`] - Converts a [`&[V; N]`][`array`] into a
///   `&TiArray<K, V, N>`.
/// - [`from_mut`] - Converts a [`&mut [V; N]`][`array`] into
///   a `&mut TiArray<K, V, N>`.
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
/// use typed_index_collections::TiArray;
///
/// #[derive(From, Into)]
/// struct FooId(usize);
///
/// let mut foos: TiArray<FooId, usize; 3> = [10, 11, 12].into();
/// assert_eq!(foos[FooId(2)], 12);
/// ```
///
/// [`from_array`]: #method.from_array
/// [`from_ref`]: #method.from_ref
/// [`from_mut`]: #method.from_mut
/// [`boxed_from`]: #method.boxed_from
/// [`boxed_into`]: #method.boxed_into
/// [`iter_enumerated`]: #method.iter_enumerated
/// [`iter_mut_enumerated`]: #method.iter_mut_enumerated
/// [`into_iter_enumerated`]: #method.into_iter_enumerated
/// [`array`]: https://doc.rust-lang.org/std/primitive.array.html
/// [`From`]: https://doc.rust-lang.org/std/convert/trait.From.html
/// [`Into`]: https://doc.rust-lang.org/std/convert/trait.Into.html
/// [`AsRef`]: https://doc.rust-lang.org/std/convert/trait.AsRef.html
/// [`AsMut`]: https://doc.rust-lang.org/std/convert/trait.AsMut.html
/// [`derive_more`]: https://crates.io/crates/derive_more
#[repr(transparent)]
pub struct TiArray<K, V, const N: usize> {
    /// Raw array property.
    pub raw: [V; N],

    /// Tied array index type.
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

macro_rules! array_impl_default {
    {$n:expr, $t:ident $($ts:ident)*} => {
        impl<K, V> Default for TiArray<K, V, { const { $n } }> where V: Default {
            #[inline]
            fn default() -> TiArray<K, V, { const { $n } }> {
                TiArray::from([$t::default(), $($ts::default()),*])
            }
        }
        array_impl_default!{($n - 1), $($ts)*}
    };
    {$n:expr,} => {
        impl<K, V> Default for TiArray<K, V, { const { $n } }> {
            #[inline]
            fn default() -> TiArray<K, V, { const { $n } }> { TiArray::from([]) }
        }
    };
}

array_impl_default! {32, V V V V V V V V V V V V V V V V V V V V V V V V V V V V V V V V}

impl<K, V, const N: usize> TiArray<K, V, N> {
    /// Converts a `[V; N]` into a `TiArray<K, V, N>`.
    ///
    /// # Example
    ///
    /// ```
    /// # use typed_index_collections::TiArray;
    /// pub struct Id(usize);
    /// let slice: TiArray<Id, usize; 3> = TiArray::from_array([1, 2, 4]);
    /// ```
    #[inline]
    pub const fn from_array(raw: [V; N]) -> Self {
        Self {
            raw,
            _marker: PhantomData,
        }
    }

    /// Converts a `&[V; N]` into a `&TiArray<K, V, N>`.
    ///
    /// # Example
    ///
    /// ```
    /// # use typed_index_collections::TiArray;
    /// pub struct Id(usize);
    /// let slice: &TiArray<Id, usize; 3> = TiArray::from_ref(&[1, 2, 4]);
    /// ```
    #[inline]
    pub const fn from_ref(raw: &[V; N]) -> &Self {
        // SAFETY: `TiArray<K, V, N>` is `repr(transparent)` over a `[V; N]` type.
        unsafe { &*(ptr::from_ref::<[V; N]>(raw).cast::<Self>()) }
    }

    /// Converts a `&mut [V; N]` into a `&mut TiArray<K, V, N>`.
    ///
    /// # Example
    ///
    /// ```
    /// # use typed_index_collections::TiArray;
    /// pub struct Id(usize);
    /// let slice: &mut TiArray<Id, usize; 3> = TiArray::from_mut(&mut [1, 2, 4]);
    /// ```
    #[inline]
    pub const fn from_mut(raw: &mut [V; N]) -> &mut Self {
        // SAFETY: `TiArray<K, V, N>` is `repr(transparent)` over a `[V; N]` type.
        unsafe { &mut *(ptr::from_mut::<[V; N]>(raw).cast::<Self>()) }
    }

    /// Converts a [`Box<[V; N], A>`][`Box`] into a `Box<TiArray<K, V, N>, A>`.
    ///
    /// # Example
    ///
    /// ```
    /// # use typed_index_collections::TiArray;
    /// pub struct Id(usize);
    /// let boxed: Box<TiArray<Id, usize; 3>> = TiArray::boxed_from(Box::new([1, 2, 4]));
    /// ```
    #[cfg(feature = "alloc")]
    #[inline]
    #[must_use]
    pub fn boxed_from<A: Allocator>(boxed: Box<[V; N], A>) -> Box<Self, A> {
        let (ptr, alloc) = Box::into_raw_with_allocator(boxed);
        // SAFETY: `TiArray<K, V, N>` is `repr(transparent)` over a `[V; N]` type.
        unsafe { Box::from_raw_in(ptr.cast::<Self>(), alloc) }
    }

    /// Converts a `Box<TiArray<K, V, N>>` into a [`Box<[V; N]>`][`Box`].
    ///
    /// # Example
    ///
    /// ```
    /// # use typed_index_collections::TiArray;
    /// pub struct Id(usize);
    /// let boxed: Box<TiArray<Id, usize; 3>> = TiArray::boxed_from(Box::new([1, 2, 4]));
    /// let boxed: Box<[usize; 3]> = boxed.boxed_into();
    /// ```
    #[cfg(feature = "alloc")]
    #[inline]
    #[must_use]
    pub fn boxed_into<A: Allocator>(self: Box<Self, A>) -> Box<[V; N], A> {
        let (ptr, alloc) = Box::into_raw_with_allocator(self);
        // SAFETY: `TiArray<K, V, N>` is `repr(transparent)` over a `[V; N]` type.
        unsafe { Box::from_raw_in(ptr.cast::<[V; N]>(), alloc) }
    }

    /// Returns an array of the same size as `self`, with function `f` applied to each element
    /// in order.
    ///
    /// See [`array::map`] for more details.
    ///
    /// [`array::map`]: https://doc.rust-lang.org/std/primitive.array.html#method.map
    #[inline]
    #[must_use]
    pub fn map<F, U>(self, f: F) -> TiArray<K, U, N>
    where
        F: FnMut(V) -> U,
    {
        TiArray::from(self.raw.map(f))
    }

    /// Returns a slice containing the entire array. Equivalent to `&s[..]`.
    ///
    /// See [`array::as_slice`] for more details.
    ///
    /// [`array::as_slice`]: https://doc.rust-lang.org/std/primitive.array.html#method.as_slice
    #[inline]
    pub const fn as_slice(&self) -> &TiSlice<K, V> {
        TiSlice::from_ref(&self.raw)
    }

    /// Returns a mutable slice containing the entire array. Equivalent to
    /// `&mut s[..]`.
    ///
    /// See [`array::as_mut_slice`] for more details.
    ///
    /// [`array::as_mut_slice`]: https://doc.rust-lang.org/std/primitive.array.html#method.as_mut_slice
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut TiSlice<K, V> {
        TiSlice::from_mut(&mut self.raw)
    }

    /// Borrows each element and returns an array of references with the same
    /// size as `self`.
    ///
    /// See [`array::each_ref`] for more details.
    ///
    /// [`array::each_ref`]: https://doc.rust-lang.org/std/primitive.array.html#method.each_ref
    #[inline]
    pub const fn each_ref(&self) -> TiArray<K, &V, N> {
        TiArray::from_array(self.raw.each_ref())
    }

    /// Borrows each element mutably and returns an array of mutable references
    /// with the same size as `self`.
    ///
    /// See [`array::each_mut`] for more details.
    ///
    /// [`array::each_mut`]: https://doc.rust-lang.org/std/primitive.array.html#method.each_mut
    #[inline]
    pub const fn each_mut(&mut self) -> TiArray<K, &mut V, N> {
        TiArray::from_array(self.raw.each_mut())
    }

    /// Converts the array into iterator over all key-value pairs
    /// with `K` used for iteration indices.
    ///
    /// It acts like `self.into_iter().enumerate()`,
    /// but use `K` instead of `usize` for iteration indices.
    ///
    /// # Example
    ///
    /// ```
    /// # use derive_more::{From, Into};
    /// # use typed_index_collections::TiArray;
    /// #[derive(Eq, Debug, From, Into, PartialEq)]
    /// pub struct Id(usize);
    /// let array: TiArray<Id, usize; 3> = [1, 2, 4].into();
    /// let mut iterator = array.into_iter_enumerated();
    /// assert_eq!(iterator.next(), Some((Id(0), 1)));
    /// assert_eq!(iterator.next(), Some((Id(1), 2)));
    /// assert_eq!(iterator.next(), Some((Id(2), 4)));
    /// assert_eq!(iterator.next(), None);
    /// ```
    #[inline]
    pub fn into_iter_enumerated(self) -> TiEnumerated<array::IntoIter<V, N>, K, V>
    where
        usize: Into<K>,
    {
        self.raw
            .into_iter()
            .enumerate()
            .map(|(key, value)| (key.into(), value))
    }
}

impl<K, V, const N: usize> Copy for TiArray<K, V, N> where V: Copy {}

impl<K, V, const N: usize> Clone for TiArray<K, V, N>
where
    V: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        self.raw.clone().into()
    }
}

impl<K, V, const N: usize> fmt::Debug for TiArray<K, V, N>
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
        f.debug_map()
            .entries(self.as_slice().iter_enumerated())
            .finish()
    }
}

impl<K, V, const N: usize> AsRef<Self> for TiArray<K, V, N> {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<K, V, const N: usize> AsMut<Self> for TiArray<K, V, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<K, V, const N: usize> AsRef<TiSlice<K, V>> for TiArray<K, V, N> {
    #[inline]
    fn as_ref(&self) -> &TiSlice<K, V> {
        TiSlice::from_ref(&self.raw)
    }
}

impl<K, V, const N: usize> AsMut<TiSlice<K, V>> for TiArray<K, V, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut TiSlice<K, V> {
        TiSlice::from_mut(&mut self.raw)
    }
}

impl<K, V, const N: usize> AsRef<[V; N]> for TiArray<K, V, N> {
    #[inline]
    fn as_ref(&self) -> &[V; N] {
        &self.raw
    }
}

impl<K, V, const N: usize> AsMut<[V; N]> for TiArray<K, V, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut [V; N] {
        &mut self.raw
    }
}

impl<K, V, const N: usize> AsRef<TiArray<K, V, N>> for [V; N] {
    #[inline]
    fn as_ref(&self) -> &TiArray<K, V, N> {
        TiArray::from_ref(self)
    }
}

impl<K, V, const N: usize> AsMut<TiArray<K, V, N>> for [V; N] {
    #[inline]
    fn as_mut(&mut self) -> &mut TiArray<K, V, N> {
        TiArray::from_mut(self)
    }
}

impl<K, V, const N: usize> AsRef<TiArray<K, MaybeUninit<V>, N>> for MaybeUninit<TiArray<K, V, N>> {
    #[inline]
    fn as_ref(&self) -> &TiArray<K, MaybeUninit<V>, N> {
        // SAFETY: `V` and `MaybeUninit<V>` have the same layout.
        unsafe { &*ptr::from_ref(self).cast() }
    }
}

impl<K, V, const N: usize> AsMut<TiArray<K, MaybeUninit<V>, N>> for MaybeUninit<TiArray<K, V, N>> {
    #[inline]
    fn as_mut(&mut self) -> &mut TiArray<K, MaybeUninit<V>, N> {
        // SAFETY: `V` and `MaybeUninit<V>` have the same layout.
        unsafe { &mut *ptr::from_mut(self).cast() }
    }
}

impl<K, V, const N: usize> AsRef<TiArray<K, Cell<V>, N>> for Cell<TiArray<K, V, N>> {
    #[inline]
    fn as_ref(&self) -> &TiArray<K, Cell<V>, N> {
        // SAFETY: `V` and `MaybeUninit<V>` have the same layout.
        unsafe { &*ptr::from_ref(self).cast() }
    }
}

impl<K, V, const N: usize> AsMut<TiArray<K, Cell<V>, N>> for Cell<TiArray<K, V, N>> {
    #[inline]
    fn as_mut(&mut self) -> &mut TiArray<K, Cell<V>, N> {
        // SAFETY: `V` and `MaybeUninit<V>` have the same layout.
        unsafe { &mut *ptr::from_mut(self).cast() }
    }
}

impl<K, V, const N: usize> Borrow<TiSlice<K, V>> for TiArray<K, V, N> {
    #[inline]
    fn borrow(&self) -> &TiSlice<K, V> {
        self.as_slice()
    }
}

impl<K, V, const N: usize> BorrowMut<TiSlice<K, V>> for TiArray<K, V, N> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut TiSlice<K, V> {
        self.as_mut_slice()
    }
}

impl<K, V, const N: usize> Eq for TiArray<K, V, N> where V: Eq {}

impl<K, A, B, const N: usize> PartialEq<TiArray<K, B, N>> for TiArray<K, A, N>
where
    A: PartialEq<B>,
{
    #[inline]
    fn eq(&self, other: &TiArray<K, B, N>) -> bool {
        self.raw == other.raw
    }
}

impl<K, A, B, const N: usize> PartialEq<&TiSlice<K, B>> for TiArray<K, A, N>
where
    A: PartialEq<B>,
{
    #[inline]
    fn eq(&self, other: &&TiSlice<K, B>) -> bool {
        self.raw == other.raw
    }
}

impl<K, A, B, const N: usize> PartialEq<&mut TiSlice<K, B>> for TiArray<K, A, N>
where
    A: PartialEq<B>,
{
    #[inline]
    fn eq(&self, other: &&mut TiSlice<K, B>) -> bool {
        self.raw == other.raw
    }
}

impl<K, V, const N: usize> Ord for TiArray<K, V, N>
where
    V: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.raw.cmp(&other.raw)
    }
}

impl<K, V, const N: usize> PartialOrd<Self> for TiArray<K, V, N>
where
    V: PartialOrd<V>,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.raw.partial_cmp(&other.raw)
    }
}

impl<K, V, const N: usize> Hash for TiArray<K, V, N>
where
    V: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

impl<K, V, const N: usize> From<[V; N]> for TiArray<K, V, N> {
    #[inline]
    fn from(array: [V; N]) -> Self {
        Self {
            raw: array,
            _marker: PhantomData,
        }
    }
}

impl<K, V, const N: usize> From<TiArray<K, V, N>> for [V; N] {
    #[inline]
    fn from(array: TiArray<K, V, N>) -> Self {
        array.raw
    }
}

impl<K, V, const N: usize> From<MaybeUninit<TiArray<K, V, N>>> for TiArray<K, MaybeUninit<V>, N> {
    #[inline]
    fn from(array: MaybeUninit<TiArray<K, V, N>>) -> Self {
        // `transmute_copy` used instead of `transmute` because Rust can not
        // prove the size equality because of `N`.
        let array = ManuallyDrop::new(array);
        // SAFETY: `TiArray<K, V, N>` is `repr(transparent)` over a `[V; N]`
        // type.
        unsafe { transmute_copy::<MaybeUninit<TiArray<K, V, N>>, Self>(&array) }
    }
}

impl<K, V, const N: usize> From<TiArray<K, MaybeUninit<V>, N>> for MaybeUninit<TiArray<K, V, N>> {
    #[inline]
    fn from(array: TiArray<K, MaybeUninit<V>, N>) -> Self {
        // `transmute_copy` used instead of `transmute` because Rust can not
        // prove the size equality because of `N`.
        let array = ManuallyDrop::new(array);
        // SAFETY: `TiArray<K, V, N>` is `repr(transparent)` over a `[V; N]`
        // type.
        unsafe { transmute_copy::<TiArray<K, MaybeUninit<V>, N>, Self>(&array) }
    }
}

// Recursive macro for implementing n-ary tuple functions and operations
//
// Also provides implementations for tuples with lesser arity. For example, tuple_impls!(A B C)
// will implement everything for (A, B, C), (A, B) and (A,).
macro_rules! tuple_impls {
    // Stopping criteria (1-ary tuple)
    ($t:ident) => {
        tuple_impls!(@impl $t);
    };

    // Running criteria (n-ary tuple, with n >= 2)
    ($t:ident $( $u:ident )+) => {
        tuple_impls!($( $u )+);
        tuple_impls!(@impl $t $( $u )+);
    };

    // "Private" internal implementation
    (@impl $( $t:ident )+) => {
        impl<K, V> From<TiArray<K, V, { const { tuple_impls!(@count $($t)+)}}>>
            for ($(tuple_impls!(@repeat V $t),)+)
        {
            #[inline]
            fn from(array: TiArray<K, V, { const { tuple_impls!(@count $($t)+)}}>) -> Self {
                let [$($t,)+] = array.raw;
                ($($t,)+)
            }
        }

        impl<K, V> From<($(tuple_impls!(@repeat V $t),)+)>
            for TiArray<K, V, { const { tuple_impls!(@count $($t)+)}}>
        {
            #[inline]
            fn from(tuple: ($(tuple_impls!(@repeat V $t),)+)) -> Self {
                let ($($t,)+) = tuple;
                Self::from([$($t,)+])
            }
        }
    };
    (@repeat $t:tt $u:tt) => {$t};
    (@count) => {
        0
    };
    (@count $t:ident $( $u:ident )*) => {
        1 + tuple_impls!(@count $($u)*)
    };
}

tuple_impls!(v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12);

impl<'a, K, V, const N: usize> TryFrom<&'a TiSlice<K, V>> for &'a TiArray<K, V, N> {
    type Error = array::TryFromSliceError;

    #[inline]
    fn try_from(slice: &'a TiSlice<K, V>) -> Result<Self, Self::Error> {
        Ok(TiArray::from_ref(<&[V; N]>::try_from(&slice.raw)?))
    }
}

impl<'a, K, V, const N: usize> TryFrom<&'a mut TiSlice<K, V>> for &'a mut TiArray<K, V, N> {
    type Error = array::TryFromSliceError;

    #[inline]
    fn try_from(slice: &'a mut TiSlice<K, V>) -> Result<Self, Self::Error> {
        Ok(TiArray::from_mut(<&mut [V; N]>::try_from(&mut slice.raw)?))
    }
}

impl<'a, K, V, const N: usize> TryFrom<&'a TiSlice<K, V>> for TiArray<K, V, N>
where
    V: Copy,
{
    type Error = array::TryFromSliceError;

    #[inline]
    fn try_from(slice: &'a TiSlice<K, V>) -> Result<Self, Self::Error> {
        Ok(*Self::from_ref(<&[V; N]>::try_from(&slice.raw)?))
    }
}

impl<'a, K, V, const N: usize> TryFrom<&'a mut TiSlice<K, V>> for TiArray<K, V, N>
where
    V: Copy,
{
    type Error = array::TryFromSliceError;

    #[inline]
    fn try_from(slice: &'a mut TiSlice<K, V>) -> Result<Self, Self::Error> {
        Ok(*Self::from_mut(<&mut [V; N]>::try_from(&mut slice.raw)?))
    }
}

impl<I, K, V, const N: usize> Index<I> for TiArray<K, V, N>
where
    TiSlice<K, V>: Index<I>,
{
    type Output = <TiSlice<K, V> as Index<I>>::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        Index::index(self.as_slice(), index)
    }
}

impl<I, K, V, const N: usize> IndexMut<I> for TiArray<K, V, N>
where
    TiSlice<K, V>: IndexMut<I>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        IndexMut::index_mut(self.as_mut_slice(), index)
    }
}

impl<K, V, const N: usize> IntoIterator for TiArray<K, V, N> {
    type Item = V;
    type IntoIter = array::IntoIter<V, N>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.raw.into_iter()
    }
}

#[expect(clippy::into_iter_without_iter, reason = "skipped in stdlib")]
impl<'a, K, V, const N: usize> IntoIterator for &'a TiArray<K, V, N> {
    type Item = &'a V;
    type IntoIter = slice::Iter<'a, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.raw.as_slice().iter()
    }
}

#[expect(clippy::into_iter_without_iter, reason = "skipped in stdlib")]
impl<'a, K, V, const N: usize> IntoIterator for &'a mut TiArray<K, V, N> {
    type Item = &'a mut V;
    type IntoIter = slice::IterMut<'a, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.raw.as_mut_slice().iter_mut()
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<K, V, const N: usize> Serialize for TiArray<K, V, N>
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
macro_rules! array_impl_deserialize {
    ($($n:literal),*) => {
        $(
            impl<'de, K, V> Deserialize<'de> for TiArray<K, V, $n>
            where
                V: Deserialize<'de>,
            {
                #[inline]
                fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where
                    D: Deserializer<'de>,
                {
                    <[V; $n]>::deserialize(deserializer).map(Into::into)
                }
            }
        )*
    };
}

array_impl_deserialize!(
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32
);

#[cfg(feature = "bincode")]
#[cfg_attr(docsrs, doc(cfg(feature = "bincode")))]
impl<K, V, const N: usize> Encode for TiArray<K, V, N>
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
impl<K, V, const N: usize, Context> Decode<Context> for TiArray<K, V, N>
where
    V: Decode<Context>,
{
    #[inline]
    fn decode<D>(decoder: &mut D) -> Result<Self, DecodeError>
    where
        D: Decoder<Context = Context>,
    {
        <[V; N]>::decode(decoder).map(Into::into)
    }
}

#[cfg(feature = "bincode")]
#[cfg_attr(docsrs, doc(cfg(feature = "bincode")))]
impl<'de, K, V, const N: usize, Context> BorrowDecode<'de, Context> for TiArray<K, V, N>
where
    V: BorrowDecode<'de, Context>,
{
    #[inline]
    fn borrow_decode<D>(decoder: &mut D) -> Result<Self, DecodeError>
    where
        D: BorrowDecoder<'de, Context = Context>,
    {
        <[V; N]>::borrow_decode(decoder).map(Into::into)
    }
}
