use crate::Index;
use core::ops;

/// A helper trait used to convert typed index ranges to `usize` ranges.
/// The trait is implemented for Rust's built-in range types with `Index` used as bound endpoints.
///
/// See [`core::ops::RangeBounds`].
///
/// [`Index`]: trait.Index.html
/// [`core::ops::RangeBounds`]: https://doc.rust-lang.org/core/ops/trait.RangeBounds.html
pub trait TiRangeBounds<K> {
    /// Appropriate usize range
    type Range: ops::RangeBounds<usize>;
    /// Converts the `TiRangeBounds` into an appropriate usize range.
    fn into_range(self) -> Self::Range;
}

impl<K: Index> TiRangeBounds<K> for ops::Range<K> {
    type Range = ops::Range<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        self.start.into_usize()..self.end.into_usize()
    }
}

impl<K: Index> TiRangeBounds<K> for ops::RangeFrom<K> {
    type Range = ops::RangeFrom<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        self.start.into_usize()..
    }
}

impl<K: Index> TiRangeBounds<K> for ops::RangeFull {
    type Range = ops::RangeFull;
    #[inline]
    fn into_range(self) -> Self::Range {
        ops::RangeFull
    }
}

impl<K: Index> TiRangeBounds<K> for ops::RangeInclusive<K> {
    type Range = ops::RangeInclusive<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        let (start, end) = self.into_inner();
        start.into_usize()..=end.into_usize()
    }
}

impl<K: Index> TiRangeBounds<K> for ops::RangeTo<K> {
    type Range = ops::RangeTo<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        ..self.end.into_usize()
    }
}

impl<K: Index> TiRangeBounds<K> for ops::RangeToInclusive<K> {
    type Range = ops::RangeToInclusive<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        ..=self.end.into_usize()
    }
}
