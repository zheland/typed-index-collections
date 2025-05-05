use core::ops;

use crate::{TiRangeBounds, TiSlice};

mod private {
    use core::ops;

    pub trait Sealed<K> {}

    impl<K> Sealed<K> for K {}
    impl<K> Sealed<K> for ops::Range<K> {}
    impl<K> Sealed<K> for ops::RangeTo<K> {}
    impl<K> Sealed<K> for ops::RangeFrom<K> {}
    impl<K> Sealed<K> for ops::RangeInclusive<K> {}
    impl<K> Sealed<K> for ops::RangeToInclusive<K> {}
    impl<K> Sealed<K> for (ops::Bound<K>, ops::Bound<K>) {}
}

/// A helper trait used for indexing operations.
///
/// This trait is implemented for `K`, [`Range<K>`], [`RangeTo<K>`],
/// [`RangeFrom<K>`], [`RangeInclusive<K>`] and [`RangeToInclusive<K>`].
/// The [`RangeFull<K>`] trait is not currently supported.
///
/// Trait implementations are only forwards to standard Rust [`slice`]
/// operations.
///
/// [`slice`]: https://doc.rust-lang.org/std/primitive.slice.html
/// [`Range<K>`]: https://doc.rust-lang.org/std/ops/struct.Range.html
/// [`RangeTo<K>`]: https://doc.rust-lang.org/std/ops/struct.RangeTo.html
/// [`RangeFrom<K>`]: https://doc.rust-lang.org/std/ops/struct.RangeFrom.html
/// [`RangeInclusive<K>`]: https://doc.rust-lang.org/std/ops/struct.RangeInclusive.html
/// [`RangeToInclusive<K>`]: https://doc.rust-lang.org/std/ops/struct.RangeToInclusive.html
/// [`RangeFull<K>`]: https://doc.rust-lang.org/std/ops/struct.RangeFull.html
pub trait TiSliceIndex<K, V>: private::Sealed<K> {
    /// The output type returned by methods.
    type Output: ?Sized;

    /// Returns a shared reference to the output at this location, if in
    /// bounds.
    fn get(self, slice: &TiSlice<K, V>) -> Option<&Self::Output>;

    /// Returns a mutable reference to the output at this location, if in
    /// bounds.
    fn get_mut(self, slice: &mut TiSlice<K, V>) -> Option<&mut Self::Output>;

    /// Returns a shared reference to the output at this location, without
    /// performing any bounds checking.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is
    /// *[undefined behavior]* even if the resulting reference is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    unsafe fn get_unchecked(self, slice: &TiSlice<K, V>) -> &Self::Output;

    /// Returns a mutable reference to the output at this location, without
    /// performing any bounds checking.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is
    /// *[undefined behavior]* even if the resulting reference is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    unsafe fn get_unchecked_mut(self, slice: &mut TiSlice<K, V>) -> &mut Self::Output;

    /// Returns a shared reference to the output at this location, panicking
    /// if out of bounds.
    fn index(self, slice: &TiSlice<K, V>) -> &Self::Output;

    /// Returns a mutable reference to the output at this location, panicking
    /// if out of bounds.
    fn index_mut(self, slice: &mut TiSlice<K, V>) -> &mut Self::Output;
}

impl<K, V> TiSliceIndex<K, V> for K
where
    usize: From<K>,
{
    type Output = V;

    #[inline]
    fn get(self, slice: &TiSlice<K, V>) -> Option<&Self::Output> {
        slice.raw.get(usize::from(self))
    }

    #[inline]
    fn get_mut(self, slice: &mut TiSlice<K, V>) -> Option<&mut Self::Output> {
        slice.raw.get_mut(usize::from(self))
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &TiSlice<K, V>) -> &Self::Output {
        // SAFETY: Guaranteed by the caller.
        unsafe { slice.raw.get_unchecked(usize::from(self)) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut TiSlice<K, V>) -> &mut Self::Output {
        // SAFETY: Guaranteed by the caller.
        unsafe { slice.raw.get_unchecked_mut(usize::from(self)) }
    }

    #[inline]
    fn index(self, slice: &TiSlice<K, V>) -> &Self::Output {
        &slice.raw[usize::from(self)]
    }

    #[inline]
    fn index_mut(self, slice: &mut TiSlice<K, V>) -> &mut Self::Output {
        &mut slice.raw[usize::from(self)]
    }
}

macro_rules! impl_ti_slice_range {
    ($ty:ty) => {
        impl<K, V> TiSliceIndex<K, V> for $ty
        where
            usize: From<K>,
        {
            type Output = TiSlice<K, V>;

            #[inline]
            fn get(self, slice: &TiSlice<K, V>) -> Option<&Self::Output> {
                slice.raw.get(self.into_range()).map(TiSlice::from_ref)
            }

            #[inline]
            fn get_mut(self, slice: &mut TiSlice<K, V>) -> Option<&mut Self::Output> {
                slice.raw.get_mut(self.into_range()).map(TiSlice::from_mut)
            }

            #[inline]
            unsafe fn get_unchecked(self, slice: &TiSlice<K, V>) -> &Self::Output {
                // SAFETY: Guaranteed by the caller.
                TiSlice::from_ref(unsafe { slice.raw.get_unchecked(self.into_range()) })
            }

            #[inline]
            unsafe fn get_unchecked_mut(self, slice: &mut TiSlice<K, V>) -> &mut Self::Output {
                // SAFETY: Guaranteed by the caller.
                TiSlice::from_mut(unsafe { slice.raw.get_unchecked_mut(self.into_range()) })
            }

            #[inline]
            fn index(self, slice: &TiSlice<K, V>) -> &Self::Output {
                TiSlice::from_ref(&slice.raw[self.into_range()])
            }

            #[inline]
            fn index_mut(self, slice: &mut TiSlice<K, V>) -> &mut Self::Output {
                TiSlice::from_mut(&mut slice.raw[self.into_range()])
            }
        }
    };
}

impl_ti_slice_range!(ops::Range<K>);
impl_ti_slice_range!(ops::RangeFrom<K>);
impl_ti_slice_range!(ops::RangeInclusive<K>);
impl_ti_slice_range!(ops::RangeTo<K>);
impl_ti_slice_range!(ops::RangeToInclusive<K>);
impl_ti_slice_range!((ops::Bound<K>, ops::Bound<K>));
