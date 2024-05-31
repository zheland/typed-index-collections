# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
- `tivec![]` macro

## [3.1.0] - 2022-09-02
### Changed
- The minimum supported Rust version has been increased to 1.46.0.
- `#[repr(transparent)]` added to `TiSlice` and `TiVec` collections.

## [3.0.3] - 2020-05-27
### Changed
- Fix description for `serde` feature flags in readme and docs.

## [3.0.2] - 2020-11-22
### Added
- `no-std` and `no-alloc` crate tests.

### Changed
- `readme-sync` dev-dependency used for docs sync check.

## [3.0.1] - 2020-10-30
### Changed
- Rephrase Introduction and About sections in readme and docs.

## [3.0.0] - 2020-10-29
### Added
- Implement `Extend` for `TiVec`.

### Changed
- Set `impl-index-from` feature always enabled because of
  compatibility issues between crates that use it and crates that don't.
- Remove `TypedIndex` trait.

## [2.0.1] - 2020-08-06
### Fixed
- Fix compilation when `serde` feature is used with `alloc` or `std` features
  without `serde/alloc` or `serde/std`.
- Use `-Z features=dev_dep` to check CI build on nightly Rust
  without features from dev-dependencies.
  See [rust-lang/cargo#1796](https://github.com/rust-lang/cargo/issues/1796)
  and [rust-lang/cargo#7916](https://github.com/rust-lang/cargo/issues/7916)
  for more details.

### Added
- Add CI build check with `std` and `serde` features.

## [2.0.0] - 2020-08-03
### Changed
- Use `AsRef::as_ref()` and `AsMut::as_mut()` instead `Into::into()`
  for zero-cost conversions between `&slice` and `&TiSlice`, `&mut slice` and `&mut TiSlice`,
  `&std::Vec` and `&TiVec`, `&mut std::Vec` and `&TiVec`.
- Migrate from Travis CI to GitHub actions.

## [1.1.0] - 2020-07-30
### Added
- `TiSlice<K, u8>` methods.

## [1.0.1] - 2020-07-25
### Added
- Example with a wrong index type that should not compile.

### Changed
- Travis config simplified.
- Simplify var names in examples.

## [1.0.0] - 2020-07-22
### Added
- Changelog.
- `TiVec::{from_ref, from_mut, drain_enumerated}` methods.
- No-op convertions between `Vec` and `TiVec` references and mutable references.
- `TiVec` API compatibility tests.
- Format and clippy checks in Travis config.

### Changed
- Improve documentation examples readability.

### Fixed
- Fix `TiSlice` and `TiVec` documentation typos.

## [0.1.2] - 2020-07-17
### Fixed
- Ignore `Cargo.lock` in repository.
- Relax `TiSlice` and `TiVec` requirements for traits
  `Default`, `Eq`, `Hash`, `Ord`, `PartialEq` and `PartialOrd`.
- Add skipped `Clone` trait implementation for `TiVec`.

## [0.1.1] - 2020-07-17
### Fixed
- Fix manifest documentation link.

## [0.1.0] - 2020-07-14
## [0.0.3] - 2020-07-14
### Added
- `TiVec::{push_and_get_key, pop_key_value}` methods.

### Fixed
- Fix previously disabled clippy lints.
- Fix broken links in documentation.
- Fix formatting in documentation.
- Fix `Index` trait requirement instead of `From` for some `TiVec` methods.

## [0.0.2] - 2020-07-13
### Fixed
- Fix typos in documentation.
- Fix skipped links in documentation.
- Fix Travis config.

## [0.0.1] - 2020-07-13
### Added
- Index trait.
- `TiSlice` wrapper for Rust `slice`.
- `TiVec` wrapper for Rust `std::vec::Vec`.
- `TiSlice` API compatibility tests.
- Crate API documentation with examples.

[Unreleased]: https://github.com/zheland/typed-index-collections/compare/v3.1.0...HEAD
[3.1.0]: https://github.com/zheland/typed-index-collections/compare/v3.0.3...v3.1.0
[3.0.3]: https://github.com/zheland/typed-index-collections/compare/v3.0.2...v3.0.3
[3.0.2]: https://github.com/zheland/typed-index-collections/compare/v3.0.1...v3.0.2
[3.0.1]: https://github.com/zheland/typed-index-collections/compare/v3.0.0...v3.0.1
[3.0.0]: https://github.com/zheland/typed-index-collections/compare/v2.0.1...v3.0.0
[2.0.1]: https://github.com/zheland/typed-index-collections/compare/v2.0.0...v2.0.1
[2.0.0]: https://github.com/zheland/typed-index-collections/compare/v1.1.0...v2.0.0
[1.1.0]: https://github.com/zheland/typed-index-collections/compare/v1.0.1...v1.1.0
[1.0.1]: https://github.com/zheland/typed-index-collections/compare/v1.0.0...v1.0.1
[1.0.0]: https://github.com/zheland/typed-index-collections/compare/v0.1.2...v1.0.0
[0.1.2]: https://github.com/zheland/typed-index-collections/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/zheland/typed-index-collections/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/zheland/typed-index-collections/compare/v0.0.3...v0.1.0
[0.0.3]: https://github.com/zheland/typed-index-collections/compare/v0.0.2...v0.0.3
[0.0.2]: https://github.com/zheland/typed-index-collections/compare/v0.0.1...v0.0.2
[0.0.1]: https://github.com/zheland/typed-index-collections/releases/tag/v0.0.1
