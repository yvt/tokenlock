//
// Copyright 2020 yvt, all rights reserved.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//
//! This crate provides a cell type, [`TokenLock`], which can only be borrowed
//! by presenting the correct unforgeable token, thus decoupling permissions
//! from data.
//!
//! # Examples
//!
//! ## Basics
//!
//! ```
//! # use tokenlock::*;
//! let mut token = IcToken::new();
//!
//! let lock: IcTokenLock<i32> = TokenLock::new(token.id(), 1);
//! assert_eq!(*lock.read(&token), 1);
//!
//! let mut guard = lock.write(&mut token);
//! assert_eq!(*guard, 1);
//! *guard = 2;
//! ```
//!
//! Only the original [`Token`]'s owner can access its contents. `Token`
//! cannot be cloned:
//!
//! ```
//! # use tokenlock::*;
//! # use std::thread;
//! # use std::sync::Arc;
//! # let mut token = ArcToken::new();
//! let lock = Arc::new(TokenLock::new(token.id(), 1));
//!
//! let lock_1 = Arc::clone(&lock);
//! thread::Builder::new().spawn(move || {
//!     let lock_1 = lock_1;
//!     let mut token_1 = token;
//!
//!     // I have `Token` so I can get a mutable reference to the contents
//!     lock_1.write(&mut token_1);
//! }).unwrap();
//!
//! // can't access the contents; I no longer have `Token`
//! // lock.write(&mut token);
//! ```
//!
//! ## Lifetimes
//!
//! The lifetime of the returned reference is limited by both of the `TokenLock`
//! and `Token`.
//!
//! ```compile_fail
//! # use tokenlock::*;
//! # use std::mem::drop;
//! let mut token = IcToken::new();
//! let lock = TokenLock::new(token.id(), 1);
//! let guard = lock.write(&mut token);
//! drop(lock); // compile error: `guard` cannot outlive `TokenLock`
//! drop(guard);
//! ```
//!
//! ```compile_fail
//! # use tokenlock::*;
//! # use std::mem::drop;
//! # let mut token = ArcToken::new();
//! # let lock = TokenLock::new(token.id(), 1);
//! # let guard = lock.write(&mut token);
//! drop(token); // compile error: `guard` cannot outlive `Token`
//! drop(guard);
//! ```
//!
//! It also prevents from forming a reference to the contained value when
//! there already is a mutable reference to it:
//!
//! ```compile_fail
//! # use tokenlock::*;
//! # let mut token = ArcToken::new();
//! # let lock = TokenLock::new(token.id(), 1);
//! let write_guard = lock.write(&mut token);
//! let read_guard = lock.read(&token); // compile error
//! drop(write_guard);
//! ```
//!
//! While allowing multiple immutable references:
//!
//! ```
//! # use tokenlock::*;
//! # let mut token = ArcToken::new();
//! # let lock = TokenLock::new(token.id(), 1);
//! let read_guard1 = lock.read(&token);
//! let read_guard2 = lock.read(&token);
//! ```
//!
//! ## Use case: Linked lists
//!
//! An operating system kernel often needs to store the global state in a global
//! variable. Linked lists are a common data structure used in a kernel, but
//! Rust's ownership does not allow forming `'static` references into values
//! protected by a mutex. Common work-arounds, such as smart pointers and index
//! references, take a heavy toll on a small microcontroller with a single-issue
//! in-order pipeline and no hardware multiplier.
//!
//! ```rust,ignore
//! struct Process {
//!     prev: Option<& /* what lifetime? */ Process>,
//!     next: Option<& /* what lifetime? */ Process>,
//!     state: u8,
//!     /* ... */
//! }
//! struct SystemState {
//!     first_process: Option<& /* what lifetime? */ Process>,
//!     process_pool: [Process; 64],
//! }
//! static STATE: Mutex<SystemState> = todo!();
//! ```
//!
//! `tokenlock` makes the `'static` reference approach possible by detaching the
//! lock granularity from the protected data's granularity.
//!
//! ```rust
//! use tokenlock::*;
//! use std::cell::Cell;
//! struct Tag;
//! impl_singleton_token_factory!(Tag);
//!
//! type KLock<T> = UnsyncSingletonTokenLock<T, Tag>;
//! type KLockToken = UnsyncSingletonToken<Tag>;
//! type KLockTokenId = SingletonTokenId<Tag>;
//!
//! struct Process {
//!     prev: KLock<Option<&'static Process>>,
//!     next: KLock<Option<&'static Process>>,
//!     state: KLock<u8>,
//!     /* ... */
//! }
//! struct SystemState {
//!     first_process: KLock<Option<&'static Process>>,
//!     process_pool: [Process; 1],
//! }
//! static STATE: SystemState = SystemState {
//!     first_process: KLock::new(KLockTokenId::new(), None),
//!     process_pool: [
//!         Process {
//!             prev: KLock::new(KLockTokenId::new(), None),
//!             next: KLock::new(KLockTokenId::new(), None),
//!             state: KLock::new(KLockTokenId::new(), 0),
//!         }
//!     ],
//! };
//! ```
//!
//! # Cell types
//!
//! The `TokenLock` type family is comprised of the following types:
//!
//! |            | `Sync` tokens    | [`!Sync` tokens]²      |
//! | ---------- | ---------------- | ---------------------- |
//! | Unpinned   | [`TokenLock`]    | [`UnsyncTokenLock`]    |
//! | Pinned¹    | [`PinTokenLock`] | [`UnsyncPinTokenLock`] |
//!
//! <sub>¹That is, these types respect `T` being `!Unpin` and prevent the
//! exposure of `&mut T` through `&Self` or `Pin<&mut Self>`.</sub>
//!
//! <sub>²`Unsync*TokenLock` require that tokens are `!Sync` (not sharable
//! across threads). In exchange, such cells can be `Sync` even if the contained
//! data is not `Sync`, just like [`std::sync::Mutex`].</sub>
//!
//! [`!Sync` tokens]: #sync-tokens
//!
//! # Token types
//!
//! This crate provides the following types implementing [`Token`].
//!
//! (**`std` only**) [`IcToken`] uses a global counter (with thread-local pools)
//! to generate unique 128-bit tokens.
//!
//! (**`alloc` only**) [`RcToken`] and [`ArcToken`] ensure their uniqueness by
//! reference-counted memory allocations.
//!
//! [`SingletonToken`]`<Tag>` is a singleton token, meaning only one of such
//! instance can exist at any point of time during the program's execution.
//! [`impl_singleton_token_factory!`] instantiates a `static` flag to indicate
//! `SingletonToken`'s liveness and allows you to construct it safely by
//! [`SingletonToken::new`]. Alternatively, you can use
//! [`SingletonToken::new_unchecked`], but this is unsafe if misused.
//!
//! [`BrandedToken`]`<'brand>` implements an extension of [`GhostCell`][1]. It's
//! created by [`with_branded_token`] or [`with_branded_token_async`], which
//! makes the created token available only within the provided closure or the
//! created `Future`. This token incurs no runtime cost.
//!
//! [1]: http://plv.mpi-sws.org/rustbelt/ghostcell/
//!
//! | Token ID (keyhole)             | Token (key)                       |
//! | ------------------------------ | --------------------------------- |
//! | [`IcTokenId`]                  | [`IcToken`] + `u128` comparison   |
//! | [`RcTokenId`]                  | [`RcToken`] + `usize` comparison  |
//! | [`ArcTokenId`]                 | [`ArcToken`] + `usize` comparison |
//! | [`SingletonTokenId`]`<Tag>`    | [`SingletonToken`]`<Tag>`         |
//! | [`BrandedTokenId`]`<'brand>`   | [`BrandedToken`]`<'brand>`        |
//!
//! # `!Sync` tokens
//!
//! [`UnsyncTokenLock`] is similar to `TokenLock` but designed for non-`Sync`
//! tokens and has relaxed requirements on the inner type for thread safety.
//! Specifically, it can be `Sync` even if the inner type is not `Sync`. This
//! allows for storing non-`Sync` cells such as [`Cell`] and reading and
//! writing them using shared references (all of which must be on the same
//! thread because the token is `!Sync`) to the token.
//!
//! [`Cell`]: crate::std_core::cell::Cell
//!
//! ```
//! # use tokenlock::*;
//! # use std::thread;
//! # use std::sync::Arc;
//! use std::cell::Cell;
//! let mut token = ArcToken::new();
//! let lock = Arc::new(UnsyncTokenLock::new(token.id(), Cell::new(1)));
//!
//! let lock_1 = Arc::clone(&lock);
//! thread::Builder::new().spawn(move || {
//!     // "Lock" the token to the current thread using
//!     // `ArcToken::borrow_as_unsync`
//!     let token = token.borrow_as_unsync();
//!
//!     // Shared references can alias
//!     let (token_1, token_2) = (&token, &token);
//!
//!     lock_1.read(token_1).set(2);
//!     lock_1.read(token_2).set(4);
//! }).unwrap();
//! ```
//!
//! `!Sync` tokens, of course, cannot be shared between threads:
//!
//! ```compile_fail
//! # use tokenlock::*;
//! # use std::thread;
//! let mut token = ArcToken::new();
//! let token = token.borrow_as_unsync();
//! let (token_1, token_2) = (&token, &token);
//!
//! // compile error: `&ArcTokenUnsyncRef` is not `Send` because
//! //                `ArcTokenUnsyncRef` is not `Sync`
//! thread::Builder::new().spawn(move || {
//!     let _ = token_2;
//! });
//!
//! let _ = token_1;
//! ```
//!
//! # Cargo Features
//!
//!  - **`std`** enables the items that depend on `std` or `alloc`.
//!  - **`alloc`** enables the items that depend on `alloc`.
//!  - **`unstable`** enables experimental items that are not subject to the
//!    semver guarantees.
//!
//! # Related Work
//!
//!  - [`ghost-cell`][1] is the official implementation of [`GhostCell`][2] and
//!    has been formally proven to be sound. It provides an equivalent of
//!    [`BrandedTokenLock`] with a simpler, more focused interface.
//!
//!  - `SCell` from [`singleton-cell`][3] is a more generalized version of
//!    `GhostCell` and accepts any singleton token types, and thus it's more
//!    closer to our `TokenLock`. It provides equivalents of our
//!    [`BrandedToken`] and [`SingletonToken`] out-of-box. It trades away
//!    non-ZST token types for an advantage: `SCell<Key, [T]>` can be transposed
//!    to `[SCell<Key, T>]`. It uses the [`singleton-trait`][5] crate (which did
//!    not exist when `tokenlock::SingletonToken` was added) to mark singleton
//!    token types.
//!
//!  - [`qcell`][4] provides multiple cell types with different check
//!    mechanisms. `QCell` uses a 32-bit integer as a token identifier, `TCell`
//!    and `TLCell` use a marker type, and `LCell` uses lifetime branding.
//!
//!  - `TokenCell` from [`token-cell`][6] is related to our [`SingletonToken`],
//!    but like `SCell` (but differing slightly), it supports transposition
//!    from `&TokenCell<Token, &[T]>` to `&[TokenCell<Token, T>]`. It uses a
//!    custom trait to mark singleton token types.
//!
//! [1]: https://crates.io/crates/ghost-cell
//! [2]: http://plv.mpi-sws.org/rustbelt/ghostcell/
//! [3]: https://crates.io/crates/singleton-cell
//! [4]: https://crates.io/crates/qcell
//! [5]: https://crates.io/crates/singleton-trait
//! [6]: https://crates.io/crates/token-cell
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "doc_cfg", feature(doc_cfg))]
#![deny(rust_2018_idioms)]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(not(feature = "std"))]
#[doc(hidden)]
pub extern crate core as std_core;
#[cfg(feature = "std")]
#[doc(hidden)]
pub extern crate std as std_core;

use self::std_core::cell::UnsafeCell;
use self::std_core::{fmt, pin::Pin};

// Modules
// ----------------------------------------------------------------------------

#[cfg(doc)]
#[doc = include_str!("../CHANGELOG.md")]
pub mod _changelog_ {}

#[cfg(feature = "alloc")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "alloc")))]
pub mod arc;
#[cfg(feature = "alloc")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "alloc")))]
pub mod rc;
#[cfg(feature = "alloc")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "alloc")))]
#[doc(no_inline)]
pub use self::{arc::*, rc::*};

#[cfg(feature = "std")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
pub mod ic;
#[cfg(feature = "std")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
#[doc(no_inline)]
pub use self::ic::*;

mod singleton_factory;

pub mod branded;
pub mod singleton;
#[doc(no_inline)]
pub use self::{branded::*, singleton::*};

#[cfg(feature = "unstable")]
mod branded_async;

// Traits
// ----------------------------------------------------------------------------

/// Trait for an unforgeable token used to access the contents of a
/// [`TokenLock`]`<_, Keyhole>`.
///
/// A token can "open" a `TokenLock` only if the token matches the metaphorical
/// keyhole.
///
/// # Safety
///
/// If safe code could obtain two instances of `T: Token<_>` `x` and `y` and an
/// instance of a `TokenLock`-like type `lock` such that `x` and `y` can be
/// mutably borrowed at the same time, and `x.eq_id(lock.keyhole()) &&
/// y.eq_id(lock.keyhole())`, it can invoke an undefined behavior by creating
/// two mutable borrows of the same place.
pub unsafe trait Token<Keyhole> {
    fn eq_id(&self, id: &Keyhole) -> bool;
}

/// Asserts the types implementing this trait are `!`[`Sync`]. (Negative bounds
/// are not supported by the compiler at the point of writing, so this trait
/// must be implemented manually.)
///
/// # Safety
///
/// `Self` must really be `!Sync`.
pub unsafe trait Unsync {}

// The `TokenLock` type family
// ----------------------------------------------------------------------------

/// A mutual exclusive primitive that can be accessed using a [`Token`]`<Keyhole>`
/// with a very low overhead.
///
/// See the [module-level documentation] for more details.
///
/// [module-level documentation]: index.html
#[derive(Default)]
pub struct TokenLock<T: ?Sized, Keyhole> {
    keyhole: Keyhole,
    data: UnsafeCell<T>,
}

// Safety: `TokenLock` does not allow more multi-thread uses of `T` than a bare
//         `T` does, so it can just inherit `T`'s `Send`-ness and `Sync`-ness
unsafe impl<T: ?Sized + Send, Keyhole: Send> Send for TokenLock<T, Keyhole> {}
unsafe impl<T: ?Sized + Send + Sync, Keyhole: Sync> Sync for TokenLock<T, Keyhole> {}

/// Like [`TokenLock`], but the usable [`Token`]s are constrained by [`Unsync`].
/// This subtle difference allows it to be `Sync` even if `T` is not.
///
/// See the [module-level documentation] for more details.
///
/// [module-level documentation]: index.html#sync-tokens
#[derive(Default)]
pub struct UnsyncTokenLock<T: ?Sized, Keyhole> {
    keyhole: Keyhole,
    data: UnsafeCell<T>,
}

// Safety: In addition to what `TokenLock`'s guarantees, Non-`Sync`-ness of
//         the `Token` prohibits `UnsyncTokenLock` from being simultaneously
//         read by multiple threads. `T: Send` is still required because `T`
//         can be moved out from any `&UnsyncTokenLock`.
unsafe impl<T: ?Sized + Send, Keyhole: Send> Send for UnsyncTokenLock<T, Keyhole> {}
unsafe impl<T: ?Sized + Send, Keyhole: Sync> Sync for UnsyncTokenLock<T, Keyhole> {}

/// A [pinned] mutual exclusive primitive that can be accessed using a
/// [`Token`]`<Keyhole>` with a very low overhead.
///
/// Unlike the unpinned variant [`TokenLock`], `PinTokenLock` does not expose
/// `&mut T` unless the receiver type is `&mut Self`. This way, the pinning
/// invariants are maintained.
///
/// See the [module-level documentation] for more details.
///
/// [pinned]: std_core::pin
/// [module-level documentation]: index.html
///
/// # Examples
///
/// ```rust
/// use std::{pin::Pin, sync::Arc};
/// use tokenlock::{ArcToken, PinTokenLock};
/// let mut token = ArcToken::new();
/// let mut value = 0;
/// let future = Arc::pin(PinTokenLock::new(token.id(), async { value = 42; }));
///
/// // Use `token` to get `Pin<&mut impl Future>`
/// futures::executor::block_on(Pin::as_ref(&future).write_pin(&mut token));
/// drop(future);
///
/// assert_eq!(value, 42);
/// ```
#[derive(Default)]
pub struct PinTokenLock<T: ?Sized, Keyhole> {
    keyhole: Keyhole,
    data: UnsafeCell<T>,
}

// Safety: See `TokenLock`.
unsafe impl<T: ?Sized + Send, Keyhole: Send> Send for PinTokenLock<T, Keyhole> {}
unsafe impl<T: ?Sized + Send + Sync, Keyhole: Sync> Sync for PinTokenLock<T, Keyhole> {}

/// Like [`PinTokenLock`], but the usable [`Token`]s are constrained by
/// [`Unsync`]. This subtle difference allows it to be `Sync` even if `T` is
/// not.
///
/// Unlike the unpinned variant [`UnsyncTokenLock`], `UnsyncPinTokenLock` does
/// not expose `&mut T` unless the receiver type is `&mut Self`. This way, the
/// [pinning] invariants are maintained.
///
/// See the [module-level documentation] for more details.
///
/// [pinning]: std_core::pin
/// [module-level documentation]: index.html#sync-tokens
#[derive(Default)]
pub struct UnsyncPinTokenLock<T: ?Sized, Keyhole> {
    keyhole: Keyhole,
    data: UnsafeCell<T>,
}

// Safety: See `UnsyncTokenLock`.
unsafe impl<T: ?Sized + Send, Keyhole: Send> Send for UnsyncPinTokenLock<T, Keyhole> {}
unsafe impl<T: ?Sized + Send, Keyhole: Sync> Sync for UnsyncPinTokenLock<T, Keyhole> {}

// Error type
// ----------------------------------------------------------------------------

/// Error type returned when a key ([`Token`]) doesn't fit in a keyhole
/// ([`TokenLock::keyhole`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BadTokenError;

#[cfg(feature = "std")]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "std")))]
impl std::error::Error for BadTokenError {
    fn description(&self) -> &str {
        "token mismatch"
    }
}

impl fmt::Display for BadTokenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "token mismatch")
    }
}

// Implementation
// ----------------------------------------------------------------------------

#[doc(hidden)]
/// Used inside [`impl_common!`].
macro_rules! if_pin {
    ( type PinTokenLock; $($rest:tt)* ) => { $($rest)* };
    ( type UnsyncPinTokenLock; $($rest:tt)* ) => { $($rest)* };
    ( type TokenLock; $($rest:tt)* ) => {};
    ( type UnsyncTokenLock; $($rest:tt)* ) => {};
}

#[doc(hidden)]
/// Used inside [`impl_common!`].
macro_rules! if_unpin {
    ( type PinTokenLock; $($rest:tt)* ) => {};
    ( type UnsyncPinTokenLock; $($rest:tt)* ) => {};
    ( type TokenLock; $($rest:tt)* ) => { $($rest)* };
    ( type UnsyncTokenLock; $($rest:tt)* ) => { $($rest)* };
}

#[doc(hidden)]
macro_rules! impl_common {
    ($ty:ident, [$($token_read_bounds:tt)*]) => {
        impl<T: ?Sized, Keyhole: fmt::Debug> fmt::Debug for $ty<T, Keyhole> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct(stringify!($ty))
                    .field("keyhole", &self.keyhole)
                    .finish()
            }
        }

        /// # Construction and Destruction
        ///
        impl<T, Keyhole> $ty<T, Keyhole> {
            /// Construct a `Self`.
            #[inline]
            pub const fn new(keyhole: Keyhole, data: T) -> Self {
                Self {
                    keyhole,
                    data: UnsafeCell::new(data),
                }
            }

            /// Construct a `Self` with a default-constructed `Keyhole`.
            #[inline]
            pub fn wrap(data: T) -> Self
            where
                Keyhole: Default,
            {
                Self::new(Default::default(), data)
            }

            /// Consume `self`, returning the contained data.
            #[inline]
            pub fn into_inner(self) -> T {
                self.data.into_inner()
            }
        }

        /// # Miscellaneous
        ///
        impl<T: ?Sized, Keyhole> $ty<T, Keyhole> {
            /// Get a reference to the contained `Keyhole` (keyhole).
            #[inline]
            pub const fn keyhole(&self) -> &Keyhole {
                &self.keyhole
            }

            /// Get a raw pointer to the contained data.
            #[inline]
            pub const fn as_ptr(&self) -> *mut T {
                self.data.get()
            }
        }

        /// # Borrowing
        ///
        impl<T: ?Sized, Keyhole> $ty<T, Keyhole> {
            // Unpinned variant:
            //
            //  - The `*_pin` methods would be unsound because the `write`
            //    method` exposes `&mut T` through `&Self`.
            //  - The `get_pin_mut` method would be unsound for the same reason.
            //
            // Pinned variant:
            //
            //  - The `write*` (non-`_pin`) method would be unsound because it
            //    exposes `&mut T` through `&Self`.
            //

            /// Get a reference to the contained data. Panic if `token` doesn't fit in
            /// the [`keyhole`](Self::keyhole).
            #[inline]
            pub fn read<'a, K: $($token_read_bounds)*>(&'a self, token: &'a K) -> &'a T {
                self.try_read(token).unwrap()
            }

            if_pin! {
                type $ty;

                /// Get a pinned reference to the contained data. Panic if `token` doesn't fit in
                /// the [`keyhole`](Self::keyhole).
                #[inline]
                pub fn read_pin<'a, K: $($token_read_bounds)*>(
                    self: Pin<&'a Self>,
                    token: &'a K,
                ) -> Pin<&'a T> {
                    self.try_read_pin(token).unwrap()
                }
            }

            if_unpin! {
                type $ty;

                /// Get a mutable reference to the contained data. Panic if `token` doesn't
                /// fit in the [`keyhole`](Self::keyhole).
                #[inline]
                pub fn write<'a, K: Token<Keyhole>>(&'a self, token: &'a mut K) -> &'a mut T {
                    self.try_write(token).unwrap()
                }
            }

            if_pin! {
                type $ty;

                /// Get a mutable pinned reference to the contained data. Panic if `token` doesn't
                /// fit in the [`keyhole`](Self::keyhole).
                #[inline]
                pub fn write_pin<'a, K: Token<Keyhole>>(
                    self: Pin<&'a Self>,
                    token: &'a mut K,
                ) -> Pin<&'a mut T> {
                    self.try_write_pin(token).unwrap()
                }
            }

            /// Get a reference to the contained data. Return `BadTokenError` if `token`
            /// doesn't fit in the [`keyhole`](Self::keyhole).
            #[inline]
            pub fn try_read<'a, K: $($token_read_bounds)*>(
                &'a self,
                token: &'a K,
            ) -> Result<&'a T, BadTokenError> {
                if token.eq_id(&self.keyhole) {
                    Ok(unsafe { &*self.data.get() })
                } else {
                    Err(BadTokenError)
                }
            }

            if_pin! {
                type $ty;

                /// Get a pinned reference to the contained data. Return `BadTokenError` if `token`
                /// doesn't fit in the [`keyhole`](Self::keyhole).
                #[inline]
                pub fn try_read_pin<'a, K: $($token_read_bounds)*>(
                    self: Pin<&'a Self>,
                    token: &'a K,
                ) -> Result<Pin<&'a T>, BadTokenError> {
                    if token.eq_id(&self.keyhole) {
                        Ok(unsafe { Pin::new_unchecked(&*self.data.get()) })
                    } else {
                        Err(BadTokenError)
                    }
                }

            }

            if_unpin! {
                type $ty;

                /// Get a mutable reference to the contained data. Return `BadTokenError` if
                /// `token` doesn't fit in the [`keyhole`](Self::keyhole).
                #[inline]
                pub fn try_write<'a, K: Token<Keyhole>>(
                    &'a self,
                    token: &'a mut K,
                ) -> Result<&'a mut T, BadTokenError> {
                    if token.eq_id(&self.keyhole) {
                        Ok(unsafe { &mut *self.data.get() })
                    } else {
                        Err(BadTokenError)
                    }
                }
            }

            if_pin! {
                type $ty;

                /// Get a mutable pinned reference to the contained data. Return `BadTokenError` if
                /// `token` doesn't fit in the [`keyhole`](Self::keyhole).
                #[inline]
                pub fn try_write_pin<'a, K: Token<Keyhole>>(
                    self: Pin<&'a Self>,
                    token: &'a mut K,
                ) -> Result<Pin<&'a mut T>, BadTokenError> {
                    if token.eq_id(&self.keyhole) {
                        Ok(unsafe { Pin::new_unchecked(&mut *self.data.get()) })
                    } else {
                        Err(BadTokenError)
                    }
                }
            }

            /// Get a mutable reference to the contained data.
            #[inline]
            pub fn get_mut(&mut self) -> &mut T {
                unsafe { &mut *self.data.get() }
            }

            if_pin! {
                type $ty;

                /// Get a mutable pinned reference to the contained data.
                #[inline]
                pub fn get_pin_mut(self: Pin<&mut Self>) -> Pin<&mut T> {
                    unsafe { Pin::new_unchecked(&mut *self.data.get()) }
                }
            }
        }

        /// # Utilities
        ///
        impl<T, Keyhole> $ty<T, Keyhole> {
            /// Get the contained data by cloning. Panic if `token` doesn't fit in
            /// the [`keyhole`](Self::keyhole).
            #[inline]
            pub fn get<K: $($token_read_bounds)*>(&self, token: &K) -> T
            where
                T: Clone,
            {
                self.read(token).clone()
            }

            /// Get the contained data by cloning. Return `BadTokenError` if `token`
            /// doesn't fit in the [`keyhole`](Self::keyhole).
            #[inline]
            pub fn try_get<K: $($token_read_bounds)*>(&self, token: &K) -> Result<T, BadTokenError>
            where
                T: Clone,
            {
                Ok(self.try_read(token)?.clone())
            }

            /// Assign a new value. Panic if `token` doesn't fit in the[`keyhole`](Self::keyhole).
            #[inline]
            pub fn set<K: Token<Keyhole>>(&self, token: &mut K, value: T) {
                self.try_set(token, value).unwrap()
            }

            /// Assign a new value. Return `BadTokenError` if `token` doesn't fit in the
            /// [`keyhole`](Self::keyhole).
            #[inline]
            pub fn try_set<K: Token<Keyhole>>(&self, token: &mut K, value: T)
                -> Result<(), BadTokenError>
            {
                if token.eq_id(&self.keyhole) {
                    // Safety: Even if the data is pinned, this is okay for the
                    // same logic as `Pin::set`.
                    Ok(unsafe { *self.data.get() = value; })
                } else {
                    Err(BadTokenError)
                }
            }

            if_unpin! {
                type $ty;

                /// Take the contained data, leaving `Default::default()` in its place.
                /// Panic if `token` doesn't fit in the [`keyhole`](Self::keyhole).
                #[inline]
                pub fn take<K: Token<Keyhole>>(&self, token: &mut K) -> T
                where
                    T: Default,
                {
                    self.replace_with(token, |_| Default::default())
                }

                /// Take the contained data, leaving `Default::default()` in its place.
                /// Return `BadTokenError` if `token` doesn't fit in the
                /// [`keyhole`](Self::keyhole).
                #[inline]
                pub fn try_take<K: Token<Keyhole>>(&self, token: &mut K) -> Result<T, BadTokenError>
                where
                    T: Default,
                {
                    self.try_replace_with(token, |_| Default::default())
                }

                /// Replace the contained data with a new one. Panic if `token` doesn't fit
                /// in the [`keyhole`](Self::keyhole).
                ///
                /// This function corresponds to [`std::mem::replace`].
                #[inline]
                pub fn replace<K: Token<Keyhole>>(&self, token: &mut K, t: T) -> T {
                    std_core::mem::replace(self.write(token), t)
                }

                /// Replace the contained data with a new one computed by the given
                /// closure. Panic if `token` doesn't fit in the
                /// [`keyhole`](Self::keyhole).
                ///
                /// This function corresponds to [`std::mem::replace`].
                #[inline]
                pub fn replace_with<K: Token<Keyhole>>(
                    &self,
                    token: &mut K,
                    f: impl FnOnce(&mut T) -> T,
                ) -> T {
                    self.try_replace_with(token, f).unwrap()
                }

                /// Replace the contained data with a new one computed by `f`. Panic if
                /// `token` doesn't fit in the [`keyhole`](Self::keyhole).
                ///
                /// This function corresponds to [`std::mem::replace`].
                #[inline]
                pub fn try_replace_with<K: Token<Keyhole>>(
                    &self,
                    token: &mut K,
                    f: impl FnOnce(&mut T) -> T,
                ) -> Result<T, BadTokenError> {
                    let inner = self.try_write(token)?;
                    let new = f(inner);
                    Ok(std_core::mem::replace(inner, new))
                }

                /// Swap the contained data with the contained data of `other`. Panic if
                /// `token` doesn't fit in the [`keyhole`](Self::keyhole) of both
                /// `TokenLock`s.
                ///
                /// This function corresponds to [`std::mem::swap`].
                #[inline]
                pub fn swap<IOther, K: Token<Keyhole> + Token<IOther>>(
                    &self,
                    token: &mut K,
                    other: &$ty<T, IOther>,
                ) {
                    self.try_swap(token, other).unwrap()
                }

                /// Swap the contained data with the contained data of `other`. Return
                /// `BadTokenError` if `token` doesn't fit in the
                /// [`keyhole`](Self::keyhole) of both `TokenLock`s.
                #[inline]
                pub fn try_swap<
                    IOther,
                    K: Token<Keyhole> + Token<IOther>>(
                    &self,
                    token: &mut K,
                    other: &$ty<T, IOther>,
                ) -> Result<(), BadTokenError> {
                    // Valiate token
                    let _ = self.try_write(token)?;
                    let _ = other.try_write(token)?;

                    // Can't take multiple loans using a single `token`, so we need raw
                    // pointers here.
                    unsafe {
                        std_core::ptr::swap(self.as_ptr(), other.as_ptr());
                    }
                    Ok(())
                }
            }
        }

        /// # Cloning
        ///
        impl<T: Clone, Keyhole: Clone> $ty<T, Keyhole> {
            /// Clone `self`. Panic if `token` doesn't fit in the
            /// [`keyhole`](Self::keyhole).
            #[inline]
            pub fn clone<K: $($token_read_bounds)*>(&self, token: &K) -> Self {
                let value = self.get(token);
                Self::new(self.keyhole.clone(), value)
            }

            /// Clone `self`. Return `BadTokenError` if `token` doesn't fit in
            /// the [`keyhole`](Self::keyhole).
            #[inline]
            pub fn try_clone<K: $($token_read_bounds)*>(&self, token: &K) -> Result<Self, BadTokenError> {
                let value = self.try_get(token)?;
                Ok(Self::new(self.keyhole.clone(), value))
            }
        }
    };
}

// `UnsyncTokenLock` has an extra `Unsync` bound on the token when a shared
// reference to a token is given. `Unsync` is not necessary if it's a mutable
// reference because a mutable reference prohibits aliasing.
impl_common!(TokenLock, [Token<Keyhole>]);
impl_common!(PinTokenLock, [Token<Keyhole>]);
impl_common!(UnsyncTokenLock, [Token<Keyhole> + Unsync]);
impl_common!(UnsyncPinTokenLock, [Token<Keyhole> + Unsync]);

// Tests
// ----------------------------------------------------------------------------

#[test]
#[cfg(feature = "alloc")]
fn basic() {
    let mut token = ArcToken::new();
    let lock = TokenLock::new(token.id(), 1);
    assert_eq!(*lock.read(&token), 1);

    let guard = lock.write(&mut token);
    assert_eq!(*guard, 1);
}

#[test]
#[cfg(feature = "alloc")]
fn bad_token() {
    let token1 = ArcToken::new();
    let mut token2 = ArcToken::new();
    let lock = TokenLock::new(token1.id(), 1);
    assert_eq!(lock.try_write(&mut token2), Err(BadTokenError));
}

#[test]
#[cfg(feature = "alloc")]
fn unsend_basic() {
    let mut token = RcToken::new();
    let lock = UnsyncTokenLock::new(token.id(), 1);
    assert_eq!(*lock.read(&token), 1);

    let guard = lock.write(&mut token);
    assert_eq!(*guard, 1);
}

#[test]
#[cfg(feature = "alloc")]
fn unsend_bad_token() {
    let token1 = RcToken::new();
    let mut token2 = RcToken::new();
    let lock = UnsyncTokenLock::new(token1.id(), 1);
    assert_eq!(lock.try_write(&mut token2), Err(BadTokenError));
}
