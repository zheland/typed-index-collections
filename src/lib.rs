//! The `typed-index-collections` crate provides [`TiSlice`] and [`TiVec`] structs
//! that are typed index versions of the Rust [`slice`] and [`std::vec::Vec`] types.
//!
//! # Introduction
//!
//! When dealing with slices and vectors it is not safe to index all arrays
//! with type-unsafe usizes as indices.
//! Using slice and vector indexing might be useful in Data Oriented Design,
//! when using Struct of Arrays, or when [`Rc`] and [`Weak`] usage is undesirable.
//!
//! # About
//!
//! This crate provides typed index version of [`slice`] and [`std::vec::Vec`]
//! types with custom index type.
//! Containers only require the index to implement [`Index`] trait.
//! If default feature `impl-index-from` is enabled, this trait is automatically implemented
//! when [`From<usize>`][`From`] and [`Into<usize>`][`Into`] are implemented.
//! And their implementation can be easily done
//! with [`derive_more`] crate and `#[derive(From, Into)]`.
//!
//! The [`TiSlice`] and [`TiVec`] structs are only wrappers
//! around Rust [`slice`] and [`std::vec::Vec`] structs with custom index type
//! and exposed `raw` property with original struct.
//! They can be easily converted to matched Rust containers using
//! [`From`], [`Into`], [`AsRef`] and [`AsMut`] traits.
//! The structs mirrors the stable API of Rust [`slice`] and [`std::vec::Vec`]
//! and forwards to it as much as possible.
//!
//! # Usage
//!
//! First, add the following to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! typed-index-collections = "2.0"
//! ```
//!
//! This crate depends on the standard library by default that is useful
//! for debugging and for some extra functionality.
//! To use this crate in a `#![no_std]` context, use `default-features = false`
//! in your `Cargo.toml` as shown below:
//!
//! ```toml
//! [dependencies.typed-index-collections]
//! version = "2.0"
//! default-features = false
//! features = ["alloc", "impl-index-from"]
//! ```
//!
//! If you want to use [`derive_more`] for
//! [`From<usize>`][`From`] and [`Into<usize>`][`Into`] implementation
//! add it to your `Cargo.toml` as shown below:
//!
//! ```toml
//! [dependencies]
//! derive_more = "0.99"
//! typed-index-collections = "2.0"
//! ```
#![cfg_attr(
    all(feature = "impl-index-from", any(feature = "alloc", feature = "std")),
    doc = r#"

    # Examples

    Simple example with [`derive_more`]:
    ```rust
    use typed_index_collections::TiVec;
    use derive_more::{From, Into};

    #[derive(From, Into)]
    struct FooId(usize);

    let mut ti_vec: TiVec<FooId, usize> = std::vec![10, 11, 13].into();
    ti_vec.insert(FooId(2), 12);
    assert_eq!(ti_vec[FooId(2)], 12);
    ```

    If a wrong index type is used, compilation will fail:
    ```compile_fail
    use typed_index_collections::TiVec;
    use derive_more::{From, Into};

    #[derive(From, Into)]
    struct FooId(usize);

    #[derive(From, Into)]
    struct BarId(usize);

    let mut ti_vec: TiVec<FooId, usize> = std::vec![10, 11, 13].into();

    ti_vec.insert(BarId(2), 12);
    //            ^^^^^^^^ expected struct `FooId`, found struct `BarId`
    assert_eq!(ti_vec[BarId(2)], 12);
    //         ^^^^^^^^^^^^^^^^ the trait ... is not implemented for `BarId`
    ```

    Another more detailed example with [`derive_more`]:
    ```rust
    use typed_index_collections::{TiSlice, TiVec};
    use derive_more::{From, Into};

    #[derive(Clone, Copy, Debug, From, Into, Eq, PartialEq)]
    struct FooId(usize);

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Foo {
        value: usize,
    }

    let first = Foo { value: 1 };
    let second = Foo { value: 2 };

    let slice_ref = &[first, second][..];
    let vec = std::vec![first, second];
    let boxed_slice = std::vec![first, second].into_boxed_slice();

    let ti_slice_ref: &TiSlice<FooId, Foo> = slice_ref.as_ref();
    let ti_vec: TiVec<FooId, Foo> = vec.into();
    let ti_boxed_slice: std::boxed::Box<TiSlice<FooId, Foo>> = boxed_slice.into();

    assert_eq!(ti_vec[FooId(1)], second);
    assert_eq!(ti_vec.raw[1], second);
    assert_eq!(ti_vec.last(), Some(&second));
    assert_eq!(ti_vec.last_key_value(), Some((FooId(1), &second)));
    assert_eq!(ti_vec.iter_enumerated().next(), Some((FooId(0), &first)));

    let _slice_ref: &[Foo] = ti_slice_ref.as_ref();
    let _vec: std::vec::Vec<Foo> = ti_vec.into();
    let _boxed_slice: std::boxed::Box<[Foo]> = ti_boxed_slice.into();
    ```
"#
)]
//!
//! # Feature Flags
//!
//! - `impl-index-from` (enabled by default) &mdash; Enables automatic [`Index`]
//!   trait implementation for types that implement
//!   [`From<usize>`][`From`] and [`Into<usize>`][`Into`].
//! - `alloc` (enabled by default) &mdash; Enables types and functions
//!   which require memory allocation.
//! - `std` (enabled by default) &mdash; Enables all [`std`] features
//!   such as memory allocations and [`std::error::Error`] trait.
//! - `serde` &mdash; Implements [`Serialize`] and [`Deserialize`] traits for slice type.
//! - `serde-alloc` &mdash; Enable [`alloc`] and `serde/alloc` features.
//! - `serde-std` &mdash; Enable [`std`] and `serde/std` features.
//!
//! # Similar crates
//!
//! - [`typed_index_collection`] provides a `Vec` wrapper with a very limited API.
//!   Indices are u32 wrappers,
//!   they are not customizable and can only index a specific type of container.
//! - [`indexed_vec`] is the closest copy of the `IndexVec` struct from `librustc_index`,
//!   but API is also different from standard Rust [`std::vec::Vec`]
//!   and it has no typed index [`slice`] alternative.
//! - [`index_vec`] have both [`slice`] and [`std::vec::Vec`] wrapper
//!   and API closer to standard API.
//!   But it implicitly allows you to use `usize` for get methods and index expressions
//!   that reduce type-safety,
//!   and the macro `define_index_type!` which is used to generate a newtyped index struct,
//!   implicitly implements a lot of traits that in my opinion would be better implemented
//!   only when necessary using crates intended for this, such as [`derive_more`].
//!
//! # License
//!
//! Licensed under either of
//!
//! - Apache License, Version 2.0
//!   ([LICENSE-APACHE](https://github.com/zheland/typed-index-collections/blob/master/LICENSE-APACHE) or
//!   [https://www.apache.org/licenses/LICENSE-2.0](https://www.apache.org/licenses/LICENSE-2.0))
//! - MIT license
//!   ([LICENSE-MIT](https://github.com/zheland/typed-index-collections/blob/master/LICENSE-MIT) or
//!   [https://opensource.org/licenses/MIT](https://opensource.org/licenses/MIT))
//!
//! at your option.
//!
//! ## Contribution
//!
//! Unless you explicitly state otherwise, any contribution intentionally submitted
//! for inclusion in the work by you, as defined in the Apache-2.0 license,
//! shall be dual licensed as above, without any
//! additional terms or conditions.
//!
//! [`TiSlice`]: struct.TiSlice.html
//! [`TiVec`]: struct.TiVec.html
//! [`Index`]: trait.Index.html
//! [`std`]: https://doc.rust-lang.org/std/index.html
//! [`alloc`]: https://doc.rust-lang.org/alloc/index.html
//! [`slice`]: https://doc.rust-lang.org/std/primitive.slice.html
//! [`Rc`]: https://doc.rust-lang.org/std/rc/struct.Rc.html
//! [`Weak`]: https://doc.rust-lang.org/std/rc/struct.Weak.html
//! [`std::vec::Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
//! [`std::error::Error`]: https://doc.rust-lang.org/std/error/trait.Error.html
//! [`From`]: https://doc.rust-lang.org/std/convert/trait.From.html
//! [`Into`]: https://doc.rust-lang.org/std/convert/trait.Into.html
//! [`AsRef`]: https://doc.rust-lang.org/std/convert/trait.AsRef.html
//! [`AsMut`]: https://doc.rust-lang.org/std/convert/trait.AsMut.html
//! [`derive_more`]: https://crates.io/crates/derive_more
//! [`typed_index_collection`]: https://crates.io/crates/typed_index_collection
//! [`indexed_vec`]: https://crates.io/crates/indexed_vec
//! [`index_vec`]: https://crates.io/crates/index_vec
//! [`Serialize`]: https://docs.serde.rs/serde/trait.Serialize.html
//! [`Deserialize`]: https://docs.serde.rs/serde/trait.Deserialize.html

#![warn(
    clippy::all,
    rust_2018_idioms,
    missing_copy_implementations,
    missing_debug_implementations,
    single_use_lifetimes,
    missing_docs,
    trivial_casts,
    unused_import_braces,
    unused_qualifications,
    unused_results
)]
#![no_std]

#[cfg(all(feature = "alloc", not(feature = "std")))]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std as alloc;

#[cfg(test)]
#[macro_use]
mod test;

mod index;
mod iter;
mod range;
mod slice;

#[cfg(any(feature = "alloc", feature = "std"))]
mod vec;

pub use index::Index;
pub use iter::{TiEnumerated, TiSliceKeys, TiSliceMutMap, TiSliceRefMap};
pub use range::TiRangeBounds;
pub use slice::{TiSlice, TiSliceIndex};

#[cfg(any(feature = "alloc", feature = "std"))]
pub use vec::TiVec;
