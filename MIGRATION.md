# Migration guide

## [2.0.0]

- Use `AsRef::as_ref()` and `AsMut::as_mut()` instead `Into::into()`
  for zero-cost conversions between `&slice` and `&TiSlice`, `&mut slice` and `&mut TiSlice`,
  `&std::Vec` and `&TiVec`, `&mut std::Vec` and `&TiVec`.

[2.0.0]: https://github.com/zheland/typed-index-collections/compare/v1.1.0...v2.0.0
