/// Creates a [`TiVec`] containing the arguments.
///
/// `ti_vec!` allows `TiVec`s to be defined with the same syntax as array
/// expressions. There are two forms of this macro:
///
/// - Create a [`TiVec`] containing a given list of elements:
///
/// ```
/// use derive_more::{From, Into};
/// use typed_index_collections::{ti_vec, TiVec};
///
/// #[derive(From, Into, Debug)]
/// struct FooId(usize);
///
/// let v: TiVec<FooId, usize> = ti_vec![1, 2, 3];
/// assert_eq!(v[FooId(0)], 1);
/// assert_eq!(v[FooId(1)], 2);
/// assert_eq!(v[FooId(2)], 3);
/// ```
///
/// - Create a [`TiVec`] from a given element and size:
///
/// ```
/// use typed_index_collections::{ti_vec, TiVec};
/// use derive_more::{From, Into};
///
/// #[derive(From, Into, Debug)]
/// struct FooId(usize);
///
/// let v: TiVec<FooId, usize> = ti_vec![1; 3];
/// assert_eq!(v.as_ref(), [1, 1, 1]);
/// ```
///
/// Note that unlike array expressions this syntax supports all elements
/// which implement [`Clone`] and the number of elements doesn't have to be
/// a constant.
///
/// This will use `clone` to duplicate an expression, so one should be careful
/// using this with types having a nonstandard `Clone` implementation. For
/// example, `ti_vec![Rc::new(1); 5]` will create a vector of five references
/// to the same boxed integer value, not five references pointing to
/// independently boxed integers.
///
/// Also, note that `ti_vec![expr; 0]` is allowed, and produces an empty vector.
/// This will still evaluate `expr`, however, and immediately drop the resulting
/// value, so be mindful of side effects.
///
/// [`TiVec`]: crate::TiVec
#[macro_export]
macro_rules! ti_vec {
    () => (
        $crate::TiVec::new()
    );
    ($elem:expr; $n:expr) => (
        $crate::TiVec::from($crate::macro_deps::vec![$elem; $n])
    );
    ($($x:expr),+ $(,)?) => (
        $crate::TiVec::from($crate::macro_deps::vec![$($x),+])
    );
}
