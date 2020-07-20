# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
- Add `CHANGELOG.md`.

### Fixed
- Improve `TiSlice` and `TiVec` documentation examples readability.

## [0.1.2] - 2020-06-17
### Fixed
- Ignore `Cargo.lock` in repository.
- Relax `TiSlice` and `TiVec` requirements for traits
  `Default`, `Eq`, `Hash`, `Ord`, `PartialEq` and `PartialOrd`.
- Add skipped `Clone` trait implementation for `TiVec`.

## [0.1.1] - 2020-06-17
### Fixed
- Fix manifest documentation link.

## [0.1.0] - 2020-06-14
## [0.0.3] - 2020-06-14
### Added
- Add `TiVec` `push_and_get_key` and `pop_key_value` methods.

### Fixed
- Fix previously disabled clippy lints.
- Fix broken links in documentation.
- Fix formatting in documentation.
- Fix `Index` trait requirement instead of `From` for some `TiVec` methods.

## [0.0.2] - 2020-06-13
### Fixed
- Fix typos in documentation.
- Fix skipped links in documentation.
- Fix Travis config.

## [0.0.1] - 2020-06-13
### Added
- Index trait.
- `TiSlice` wrapper for Rust `slice`.
- `TiVec` wrapper for Rust `std::vec::Vec`.
- `TiSlice` API compatibility tests.
- Crate API documentation with examples.

[Unreleased]: https://github.com/zheland/typed-index-collections/compare/v0.1.2...HEAD
[0.1.2]: https://github.com/zheland/typed-index-collections/compare/v0.1.1...v0.1.2
[0.1.1]: https://github.com/zheland/typed-index-collections/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/zheland/typed-index-collections/compare/v0.0.3...v0.1.0
[0.0.3]: https://github.com/zheland/typed-index-collections/compare/v0.0.2...v0.0.3
[0.0.2]: https://github.com/zheland/typed-index-collections/compare/v0.0.1...v0.0.2
[0.0.1]: https://github.com/zheland/typed-index-collections/releases/tag/v0.0.1
