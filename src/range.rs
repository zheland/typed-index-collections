use core::ops;

/// A helper trait used to convert typed index ranges to `usize` ranges.
/// The trait is implemented for Rust's built-in range types with `K where usize: `[`From<K>`] used as bound endpoints.
///
/// See [`core::ops::RangeBounds`] for more details.
///
/// [`From<K>`]: https://doc.rust-lang.org/std/convert/trait.From.html
/// [`core::ops::RangeBounds`]: https://doc.rust-lang.org/core/ops/trait.RangeBounds.html
pub trait TiRangeBounds<K> {
    /// Appropriate usize range
    type Range: ops::RangeBounds<usize>;
    /// Converts the `TiRangeBounds` into an appropriate usize range.
    fn into_range(self) -> Self::Range;
}

impl<K> TiRangeBounds<K> for ops::Range<K>
where
    usize: From<K>,
{
    type Range = ops::Range<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        self.start.into()..self.end.into()
    }
}

impl<K> TiRangeBounds<K> for ops::RangeFrom<K>
where
    usize: From<K>,
{
    type Range = ops::RangeFrom<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        self.start.into()..
    }
}

impl<K> TiRangeBounds<K> for ops::RangeFull
where
    usize: From<K>,
{
    type Range = Self;
    #[inline]
    fn into_range(self) -> Self::Range {
        Self
    }
}

impl<K> TiRangeBounds<K> for ops::RangeInclusive<K>
where
    usize: From<K>,
{
    type Range = ops::RangeInclusive<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        let (start, end) = self.into_inner();
        start.into()..=end.into()
    }
}

impl<K> TiRangeBounds<K> for ops::RangeTo<K>
where
    usize: From<K>,
{
    type Range = ops::RangeTo<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        ..self.end.into()
    }
}

impl<K> TiRangeBounds<K> for ops::RangeToInclusive<K>
where
    usize: From<K>,
{
    type Range = ops::RangeToInclusive<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        ..=self.end.into()
    }
}
