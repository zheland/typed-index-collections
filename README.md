# typed-index-collections

![CI](https://github.com/zheland/typed-index-collections/workflows/CI/badge.svg)
[![Latest Version](https://img.shields.io/crates/v/typed-index-collections.svg)](https://crates.io/crates/typed-index-collections)
[![docs.rs](https://docs.rs/typed-index-collections/badge.svg)](https://docs.rs/typed-index-collections)
[![GitHub license](https://img.shields.io/crates/l/typed-index-collections)](https://github.com/zheland/typed-index-collections/#license)
[![Rust Version](https://img.shields.io/badge/rustc-1.41+-lightgray.svg)](https://blog.rust-lang.org/2020/01/30/Rust-1.41.0.html)

The `typed-index-collections` crate provides [`TiSlice`] and [`TiVec`] structs
that are typed index versions of the Rust [`slice`] and [`std::vec::Vec`] types.

## Introduction

When dealing with slices and vectors it is not safe to index all arrays
with type-unsafe usizes as indices.
Using slice and vector indexing might be useful in Data Oriented Design,
when using Struct of Arrays, or when [`Rc`] and [`Weak`] usage is undesirable.

## About

This crate provides typed index version of [`slice`] and [`std::vec::Vec`]
types with custom index type.
Containers only require the index to implement
[`From<usize>`][`From`] and [`Into<usize>`][`Into`] traits.
Their implementation can be easily done
with [`derive_more`] crate and `#[derive(From, Into)]`.

The [`TiSlice`] and [`TiVec`] structs are only wrappers
around Rust [`slice`] and [`std::vec::Vec`] structs with custom index type
and exposed `raw` property with original struct.
They can be easily converted to matched Rust containers using
[`From`], [`Into`], [`AsRef`] and [`AsMut`] traits.
The structs mirrors the stable API of Rust [`slice`] and [`std::vec::Vec`]
and forwards to it as much as possible.

## Usage

First, add the following to your `Cargo.toml`:

```toml
[dependencies]
typed-index-collections = "3.0"
```

This crate depends on the standard library by default that is useful
for debugging and for some extra functionality.
To use this crate in a `#![no_std]` context, use `default-features = false`
in your `Cargo.toml` as shown below:

```toml
[dependencies.typed-index-collections]
version = "3.0"
default-features = false
features = ["alloc"]
```

If you want to use [`derive_more`] for
[`From<usize>`][`From`] and [`Into<usize>`][`Into`] implementation
add it to your `Cargo.toml` as shown below:

```toml
[dependencies]
derive_more = "0.99"
typed-index-collections = "3.0"
```

## Examples

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
```rust
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

## Documentation

[API Documentation]

## Feature Flags

- `alloc` (enabled by default) &mdash; Enables types and functions
  which require memory allocation.
- `std` (enabled by default) &mdash; Enables all [`std`] features
  such as memory allocations, [`std::error::Error`] trait and
  [`std::panic::UnwindSafe`] trait implementations.
- `serde` &mdash; Implements [`Serialize`] and [`Deserialize`] traits
  for slice primitive and [`Serialize`] trait for [`std::vec::Vec`] container.
- `serde-alloc` &mdash; Enable [`alloc`] and `serde/alloc` features and
  implement [`Deserialize`] trait for [`std::vec::Vec`] container.
- `serde-std` &mdash; Enable [`std`] and `serde/std` features and
  implement [`Deserialize`] trait for [`std::vec::Vec`] container.

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
  implicitly implements a lot of traits that in my opinion would be better implemented
  only when necessary using crates intended for this, such as [`derive_more`].

## License

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or
  [https://www.apache.org/licenses/LICENSE-2.0](https://www.apache.org/licenses/LICENSE-2.0))
- MIT license
  ([LICENSE-MIT](LICENSE-MIT) or
  [https://opensource.org/licenses/MIT](https://opensource.org/licenses/MIT))

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license,
shall be dual licensed as above, without any
additional terms or conditions.

[`TiSlice`]: https://docs.rs/typed-index-collections/*/typed_index_collections/struct.TiSlice.html
[`TiVec`]: https://docs.rs/typed-index-collections/*/typed_index_collections/struct.TiVec.html
[API Documentation]: https://docs.rs/typed-index-collections
[`std`]: https://doc.rust-lang.org/std/index.html
[`alloc`]: https://doc.rust-lang.org/alloc/index.html
[`slice`]: https://doc.rust-lang.org/std/primitive.slice.html
[`Rc`]: https://doc.rust-lang.org/std/rc/struct.Rc.html
[`Weak`]: https://doc.rust-lang.org/std/rc/struct.Weak.html
[`std::vec::Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
[`std::error::Error`]: https://doc.rust-lang.org/std/error/trait.Error.html
[`std::panic::UnwindSafe`]: https://doc.rust-lang.org/std/panic/trait.UnwindSafe.html
[`From`]: https://doc.rust-lang.org/std/convert/trait.From.html
[`Into`]: https://doc.rust-lang.org/std/convert/trait.Into.html
[`AsRef`]: https://doc.rust-lang.org/std/convert/trait.AsRef.html
[`AsMut`]: https://doc.rust-lang.org/std/convert/trait.AsMut.html
[`derive_more`]: https://crates.io/crates/derive_more
[`typed_index_collection`]: https://crates.io/crates/typed_index_collection
[`indexed_vec`]: https://crates.io/crates/indexed_vec
[`index_vec`]: https://crates.io/crates/index_vec
[`Serialize`]: https://docs.serde.rs/serde/trait.Serialize.html
[`Deserialize`]: https://docs.serde.rs/serde/trait.Deserialize.html
