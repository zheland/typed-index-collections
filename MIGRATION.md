# Migration guide

## [4.0.0]
- Some methods now require specifying a generic parameter for the allocator.
  It is usually determined automatically via type inference.
- Futures `serde-alloc` and `serde-std` have been removed.
  Use combination of `serde`, `alloc`, `std` instead.
- `TiVec::extend_from_within` method now requires proper `R: TiRangeBounds<K>`
  bounds.

## [3.0.0]
- Default `impl-index-from` feature is now always enabled.
  Use wrappers for `TypedIndex` values
  if you use different `From/Into` `usize` and `TypedIndex::{from_usize, into_usize}` implementations.
- Trait `TypedIndex` was removed.
  Use `From<usize>` and `Into<usize>` instead.

## [2.0.0]
- Use `TiSlice::from_ref()`, `TiSlice::from_mut()`,
  `AsRef::as_ref()` and `AsMut::as_mut()` instead `Into::into()`
  for zero-cost conversions between `&slice` and `&TiSlice`, `&mut slice` and `&mut TiSlice`,
  `&std::Vec` and `&TiVec`, `&mut std::Vec` and `&TiVec`.

[4.0.0]: https://github.com/zheland/typed-index-collections/compare/v3.5.0...v4.0.0
[3.0.0]: https://github.com/zheland/typed-index-collections/compare/v2.0.1...v3.0.0
[2.0.0]: https://github.com/zheland/typed-index-collections/compare/v1.1.0...v2.0.0
