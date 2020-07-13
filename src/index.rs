/// A trait for [`TiSlice`] and [`TiVec`] indeces.
///
/// If default feature `impl-index-from` is enabled, this trait is automatically implemented
/// when [`From<usize>`] and [`Into<usize>`] are implemented.
/// And their implementation can be easily done
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

/// The `Index` trait is automatically implemented for types which implement [`From<usize>`] and [`Into<usize>`] only when `impl-index-from` feature is enabled.
///
/// With `default-features = false` you can opt-out of
/// the [`From`] and [`Into`] implementation which in some cases is not desirable.
///
/// [`From`]: https://doc.rust-lang.org/std/convert/trait.From.html
/// [`Into`]: https://doc.rust-lang.org/std/convert/trait.Into.html
/// [`From<usize>`]: https://doc.rust-lang.org/std/convert/trait.From.html
/// [`Into<usize>`]: https://doc.rust-lang.org/std/convert/trait.Into.html
#[cfg(feature = "impl-index-from")]
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
