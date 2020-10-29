# Migration guide

## [Unreleased]
- Default `impl-index-from` feature is now always enabled.
  Use wrappers for `TypedIndex` values
  if you use different `From/Into` `usize` and `TypedIndex::{from_usize, into_usize}` implementations.

## [2.0.0]
- Use `AsRef::as_ref()` and `AsMut::as_mut()` instead `Into::into()`
  for zero-cost conversions between `&slice` and `&TiSlice`, `&mut slice` and `&mut TiSlice`,
  `&std::Vec` and `&TiVec`, `&mut std::Vec` and `&TiVec`.

[Unreleased]: https://github.com/zheland/typed-index-collections/compare/v2.0.1...HEAD
[2.0.0]: https://github.com/zheland/typed-index-collections/compare/v1.1.0...v2.0.0
