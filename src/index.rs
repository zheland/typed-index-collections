/// A trait for [`TiSlice`] and [`TiVec`] indeces.
///
/// This trait is automatically implemented
/// when [`From<usize>`] and [`Into<usize>`] are implemented.
/// Their implementation can be easily done
/// with [`derive_more`] crate and `#[derive(From, Into)]`.
///
/// [`TiSlice`]: struct.TiSlice.html
/// [`TiVec`]: struct.TiVec.html
/// [`From<usize>`]: https://doc.rust-lang.org/std/convert/trait.From.html
/// [`Into<usize>`]: https://doc.rust-lang.org/std/convert/trait.Into.html
/// [`derive_more`]: https://crates.io/crates/derive_more
pub trait Index {
    /// Construct an Index from a usize.
    fn from_usize(index: usize) -> Self;
    /// Get the underlying index.
    fn into_usize(self) -> usize;
}

impl<T> Index for T
where
    T: From<usize>,
    usize: From<T>,
{
    fn from_usize(index: usize) -> Self {
        Self::from(index)
    }

    fn into_usize(self) -> usize {
        self.into()
    }
}
