# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- `IcToken` (counter-based tokens)
- `BrandedToken` and `with_branded_token` (a GhostCell implementation)
- (Unstable) `with_branded_token_async`
- `TokenLock::wrap`, a constructor that default-initializes `Keyhole: TokenId`, provided for convenience
- `impl Display for {BadTokenError, SingletonTokenExhaustedError}` when `cfg(not(feature = "std"))`
- `[Unsync]PinTokenLock`
- `*TokenLock::{set, try_set}`
- `SingletonTokenLock<T, Tag>` (an alias of `TokenLock<T, SingletonTokenId<Tag>>`) and its variations
- `impl_singleton_token_factory!` can now be applied to multiple types in a single macro call

### Changed

- Raise the minimum supported Rust version to 1.54.0 (MSRV changes are not considered semver-breaking anymore.)

## [0.3.4] - 2021-01-31

### Fixed

- Preserve the `Sync`-ness variant when `Deref`-ing a `SingletonTokenRefMut`

## [0.3.3] - 2021-01-31

### Fixed

- Fixed the crate failing to compile when building without `std` feature

## [0.3.2] - 2021-01-31

### Added

- [`SingletonToken`](https://docs.rs/tokenlock/0.3.2/tokenlock/struct.SingletonToken.html), a zero-sized token type
- [`UnsyncTokenLock`](https://docs.rs/tokenlock/0.3.2/tokenlock/struct.UnsyncTokenLock.html), which has more lenient requirements for `Sync`-ness provided that the token type is `!Sync`. You can store a `Cell` in `UnsyncTokenLock`, which will still be `Sync`.

### Changed

- Relaxed the requirements for `TokenLock: Send, Sync`.

## [0.3.1] - 2020-06-13

- Update `README.md`

## [0.3.0] - 2020-06-06

- **Breaking**: Raise the minimum supported Rust version to 1.34.2
- **Breaking**: Rename `TokenLock::{read → try_read, write → try_write}`, introducing a panicking variation `TokenLock::{read, write}` of these methods
- Add `TokenLock::{get, try_get, replace, replace_with, try_replace_with, clone, try_clone, swap, try_swap, take, try_take}`
- Implement `Default`

## [0.2.3] - 2020-06-06

- Add `TokenLock::{as_ptr, into_inner}`
- Support `no_std`

## 0.1.6 - 20xx-xx-xx

[Unreleased]: https://github.com/yvt/tokenlock/compare/0.3.4...HEAD
[0.3.4]: https://github.com/yvt/tokenlock/compare/0.3.3...0.3.4
[0.3.3]: https://github.com/yvt/tokenlock/compare/0.3.2...0.3.3
[0.3.2]: https://github.com/yvt/tokenlock/compare/0.3.1...0.3.2
[0.3.1]: https://github.com/yvt/tokenlock/compare/0.3.0...0.3.1
[0.3.0]: https://github.com/yvt/tokenlock/compare/0.2.3...0.3.0
[0.2.3]: https://github.com/yvt/tokenlock/compare/0.1.6...0.2.3
