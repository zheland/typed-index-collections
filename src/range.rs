use core::ops;

/// A helper trait used to convert typed index ranges to `usize` ranges.
/// The trait is implemented for Rust's built-in range types with
/// `K: `[`Into<usize>`] used as bound endpoints.
///
/// See [`core::ops::RangeBounds`] for more details.
///
/// [`Into<usize>`]: https://doc.rust-lang.org/std/convert/trait.Into.html
/// [`core::ops::RangeBounds`]: https://doc.rust-lang.org/core/ops/trait.RangeBounds.html
pub trait TiRangeBounds<K> {
    /// Appropriate usize range
    type Range: ops::RangeBounds<usize>;
    /// Converts the `TiRangeBounds` into an appropriate usize range.
    fn into_range(self) -> Self::Range;
}

impl<K> TiRangeBounds<K> for ops::Range<K>
where
    K: Into<usize>,
{
    type Range = ops::Range<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        self.start.into()..self.end.into()
    }
}

impl<K> TiRangeBounds<K> for ops::RangeFrom<K>
where
    K: Into<usize>,
{
    type Range = ops::RangeFrom<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        self.start.into()..
    }
}

impl<K> TiRangeBounds<K> for ops::RangeFull
where
    K: Into<usize>,
{
    type Range = Self;
    #[inline]
    fn into_range(self) -> Self::Range {
        Self
    }
}

impl<K> TiRangeBounds<K> for ops::RangeInclusive<K>
where
    K: Into<usize>,
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
    K: Into<usize>,
{
    type Range = ops::RangeTo<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        ..self.end.into()
    }
}

impl<K> TiRangeBounds<K> for ops::RangeToInclusive<K>
where
    K: Into<usize>,
{
    type Range = ops::RangeToInclusive<usize>;
    #[inline]
    fn into_range(self) -> Self::Range {
        ..=self.end.into()
    }
}

impl<K> TiRangeBounds<K> for (ops::Bound<K>, ops::Bound<K>)
where
    K: Into<usize>,
{
    type Range = (ops::Bound<usize>, ops::Bound<usize>);
    #[inline]
    fn into_range(self) -> Self::Range {
        (map_bound(self.0), map_bound(self.1))
    }
}

#[inline]
fn map_bound<K>(bound: ops::Bound<K>) -> ops::Bound<usize>
where
    K: Into<usize>,
{
    match bound {
        ops::Bound::Included(index) => ops::Bound::Included(index.into()),
        ops::Bound::Excluded(index) => ops::Bound::Excluded(index.into()),
        ops::Bound::Unbounded => ops::Bound::Unbounded,
    }
}
