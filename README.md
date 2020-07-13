# typed-index-collections

[![build status](https://travis-ci.org/zheland/typed-index-collections.svg?branch=master)](https://travis-ci.org/zheland/typed-index-collections)
[![Latest Version](https://img.shields.io/crates/v/typed-index-collections.svg)](https://crates.io/crates/typed-index-collections)
[![docs.rs](https://docs.rs/typed-index-collections/badge.svg)](https://docs.rs/typed-index-collections)
[![GitHub license](https://img.shields.io/crates/l/typed-index-collections)](https://github.com/zheland/typed-index-collections/#license)
[![Rust Version](https://img.shields.io/badge/rustc-1.41+-lightgray.svg)](https://blog.rust-lang.org/2020/01/30/Rust-1.41.0.html)

The `typed-index-collections` crate provides
typed index version of the Rust [`slice`] and [`std::vec::Vec`] types.

## Introduction

When dealing with slices and vectors it is not safe to index all arrays
with type-unsafe usizes as indices.
Using slice and vector indexing might be useful in Data Oriented Design,
when using Struct of Arrays, or when `Rc` and `Weak` usage is undesirable.

## About

This crate provides typed index version of [`slice`] and [`std::vec::Vec`]
types with custom index type.
Containers only require the index to implement [`Index`] trait.
If default feature `impl-index-from` is enabled, this trait is automatically implemented
when [`From<usize>`] and [`Into<usize>`] are implemented.
And their implementation can be easily done
with [`derive_more`] crate and `#[derive(From, Into)]`.

The [`TiSlice`] and [`TiVec`] structs are only wrappers
around Rust [`slice`] and [`std::vec::Vec`] structs with custom index type
and exposed `raw` property with original struct.
They can be easily converted to matched Rust containers using [`From`] and [`Into`] traits.
The structs mirrors the stable API of Rust [`slice`] and [`std::vec::Vec`]
and forwards to it as much as possible.

## Usage

First, add the following to your `Cargo.toml`:

```toml
[dependencies]
typed-index-collections = "0.0.2"
```

This crate depends on the standard library by default that is useful
for debugging and for some extra functionality.
To use this crate in a `#![no_std]` context, use `default-features = false`
in your `Cargo.toml` as shown below:

```toml
[dependencies.typed-index-collections]
version = "0.0.2"
default-features = false
features = ["alloc", "impl-index-from"]
```

If you want to use [`derive_more`] for [`From<usize>`] and [`Into<usize>`] implementation
add it to your `Cargo.toml` as shown below:

```toml
[dependencies]
derive_more = "0.99"
typed-index-collections = "0.0.2"
```

## Examples

Simple example with [`derive_more`]:
```rust
use typed_index_collections::TiVec;
use derive_more::{From, Into};

#[derive(From, Into)]
struct FooId(usize);

let mut foos: TiVec<FooId, usize> = std::vec![10, 11, 13].into();
foos.insert(FooId(2), 12);
assert_eq!(foos[FooId(2)], 12);
```

Another example with [`derive_more`]:
```rust
use typed_index_collections::{TiSlice, TiVec};
use derive_more::{From, Into};

#[derive(Clone, Copy, Debug, From, Into, Eq, PartialEq)]
struct FooId(usize);

#[derive(Clone, Copy, Debug, From, Into, Eq, PartialEq)]
struct BarId(usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Foo {
    value: usize,
}

let first = Foo { value: 1 };
let second = Foo { value: 2 };

let slice_ref = &[first, second][..];
let vec = std::vec![first, second];
let boxed_slice = std::vec![first, second].into_boxed_slice();

let typed_index_slice_ref: &TiSlice<FooId, Foo> = slice_ref.into();
let typed_index_vec: TiVec<FooId, Foo> = vec.into();
let typed_index_boxed_slice: std::boxed::Box<TiSlice<FooId, Foo>> = boxed_slice.into();

assert_eq!(typed_index_vec[FooId(1)], second);
assert_eq!(typed_index_vec.raw[1], second);
assert_eq!(typed_index_vec.last(), Some(&second));
assert_eq!(typed_index_vec.last_key_value(), Some((FooId(1), &second)));
assert_eq!(
    typed_index_vec.iter_enumerated().next(),
    Some((FooId(0), &first))
);
// assert_eq!(vec[BarId(1)], second); // won't compile with incompable index

let _slice_ref: &[Foo] = typed_index_slice_ref.into();
let _vec: std::vec::Vec<Foo> = typed_index_vec.into();
let _boxed_slice: std::boxed::Box<[Foo]> = typed_index_boxed_slice.into();
```

## Documentation

[API Documentation]

## Feature Flags

- `impl-index-from` (enabled by default) &mdash; Enables automatic [`Index`]
  trait implementation for types that implement [`From<usize>`] and [`Into<usize>`].
- `alloc` (enabled by default) &mdash; Enables types and functions
  which require memory allocation.
- `std` (enabled by default) &mdash; Enables all [`std`] features
  such as memory allocations and [`std::error::Error`] trait.
- `serde` &mdash; Implements [`Serialize`] and [`Deserialize`] traits for slice type.
- `serde-alloc` &mdash; Enable [`alloc`] and `serde/alloc` features.
- `serde-std` &mdash; Enable [`std`] and `serde/std` features.

## Similar crates

- [`typed_index_collection`] provides a `Vec` wrapper with a very limited API.
  Indices are u32 wrappers,
  they are not customizable and can only index a specific type of container.
- [`indexed_vec`] is the closest copy of the `IndexVec` struct from `librustc_index`,
  but API is also different from standard Rust [`std::vec::Vec`]
  and it has no typed index [`slice`] alternative.
- [`index_vec`] have both [`slice`] and [`std::vec::Vec`] wrapper
  and API closer to standard API.
  But it implicitly allows you to use `usize` for get methods and index expressions
  that reduce type-safety,
  and the macro `define_index_type!` which is used to generate a newtyped index struct,
  implicitly implements a lot of traits that would be better implemented
  only when necessary using crates intended for this, such as [`derive_more`].

## License

Licensed under either of

- Apache License, Version 2.0,
  ([LICENSE-APACHE](LICENSE-APACHE) or
  [https://www.apache.org/licenses/LICENSE-2.0](https://www.apache.org/licenses/LICENSE-2.0))
- MIT license ([LICENSE-MIT](LICENSE-MIT) or
  [https://opensource.org/licenses/MIT](https://opensource.org/licenses/MIT))

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license,
shall be dual licensed as above, without any
additional terms or conditions.

[`TiSlice`]: https://docs.rs/typed-index-collections/*/typed_index_collections/struct.TiSlice.html
[`TiVec`]: https://docs.rs/typed-index-collections/*/typed_index_collections/struct.TiVec.html
[`Index`]: https://docs.rs/typed-index-collections/*/typed_index_collections/trait.Index.html
[API Documentation]: https://docs.rs/typed-index-collections
[`std`]: https://doc.rust-lang.org/std/index.html
[`alloc`]: https://doc.rust-lang.org/alloc/index.html
[`slice`]: https://doc.rust-lang.org/std/primitive.slice.html
[`std::vec::Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
[`std::error::Error`]: https://doc.rust-lang.org/std/error/trait.Error.html
[`From`]: https://doc.rust-lang.org/std/convert/trait.From.html
[`Into`]: https://doc.rust-lang.org/std/convert/trait.Into.html
[`From<usize>`]: https://doc.rust-lang.org/std/convert/trait.From.html
[`Into<usize>`]: https://doc.rust-lang.org/std/convert/trait.Into.html
[`derive_more`]: https://crates.io/crates/derive_more
[`typed_index_collection`]: https://crates.io/crates/typed_index_collection
[`indexed_vec`]: https://crates.io/crates/indexed_vec
[`index_vec`]: https://crates.io/crates/index_vec
[`Serialize`]: https://docs.serde.rs/serde/trait.Serialize.html
[`Deserialize`]: https://docs.serde.rs/serde/trait.Deserialize.html
