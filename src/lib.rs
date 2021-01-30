//
// Copyright 2020 yvt, all rights reserved.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//
//! Provides a cell type whose contents can be accessed only using an
//! unforgeable token.
//!
//! # Examples
//!
//! ```
//! # use tokenlock::*;
//! let mut token = ArcToken::new();
//!
//! let lock = TokenLock::new(token.id(), 1);
//! assert_eq!(*lock.read(&token), 1);
//!
//! let mut guard = lock.write(&mut token);
//! assert_eq!(*guard, 1);
//! *guard = 2;
//! ```
//!
//! Only the original `Token`'s owner can access its contents. `Token`
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
//! The lifetime of the returned reference is limited by both of the `TokenLock`
//! and `Token`.
//!
//! ```compile_fail
//! # use tokenlock::*;
//! # use std::mem::drop;
//! let mut token = ArcToken::new();
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
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
#[doc(hidden)]
pub extern crate core as std_core;
#[cfg(feature = "std")]
#[doc(hidden)]
pub extern crate std as std_core;

use self::std_core::cell::UnsafeCell;
use self::std_core::fmt;

#[cfg(feature = "std")]
mod arc;
#[cfg(feature = "std")]
mod rc;
#[cfg(feature = "std")]
pub use self::{arc::*, rc::*};

mod singleton;
mod singleton_factory;
pub use self::{singleton::*, singleton_factory::*};

/// Trait for an unforgeable token used to access the contents of a
/// [`TokenLock`]`<_, Keyhole>`.
///
/// A token can "open" a `TokenLock` only if the token matches the metaphorical
/// keyhole.
///
/// # Safety
///
/// Given two distinct instances of `T: Token` `x` and `y`,
/// `x.eq_id(i) && y.eq_id(i)` must not be `true` for any `i`.
pub unsafe trait Token<Keyhole> {
    fn eq_id(&self, id: &Keyhole) -> bool;
}

/// A mutual exclusive primitive that can be accessed using a [`Token`]`<Keyhole>`
/// with a very low over-head.
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
unsafe impl<T: ?Sized + Sync, Keyhole: Sync> Sync for TokenLock<T, Keyhole> {}

impl<T: ?Sized, Keyhole: fmt::Debug> fmt::Debug for TokenLock<T, Keyhole> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TokenLock")
            .field("keyhole", &self.keyhole)
            .finish()
    }
}

/// Error type returned when a key ([`Token`]) doesn't fit in a keyhole
/// ([`TokenLock::keyhole`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BadTokenError;

#[cfg(feature = "std")]
impl std::error::Error for BadTokenError {
    fn description(&self) -> &str {
        "token mismatch"
    }
}

#[cfg(feature = "std")]
impl fmt::Display for BadTokenError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "token mismatch")
    }
}

impl<T, Keyhole> TokenLock<T, Keyhole> {
    /// Construct a `TokenLock`.
    pub const fn new(keyhole: Keyhole, data: T) -> Self {
        Self {
            keyhole,
            data: UnsafeCell::new(data),
        }
    }

    /// Consume this `TokenLock`, returning the contained data.
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized, Keyhole> TokenLock<T, Keyhole> {
    /// Get a reference to the contained `Keyhole` (keyhole).
    #[inline]
    pub const fn keyhole(&self) -> &Keyhole {
        &self.keyhole
    }

    /// Get a mutable reference to the contained data.
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data.get() }
    }

    /// Get a raw pointer to the contained data.
    #[inline]
    pub const fn as_ptr(&self) -> *mut T {
        self.data.get()
    }

    /// Get a reference to the contained data. Panic if `token` doesn't fit in
    /// the [`keyhole`](TokenLock::keyhole).
    #[inline]
    pub fn read<'a, K: Token<Keyhole>>(&'a self, token: &'a K) -> &'a T {
        self.try_read(token).unwrap()
    }

    /// Get a mutable reference to the contained data. Panic if `token` doesn't
    /// fit in the [`keyhole`](TokenLock::keyhole).
    #[inline]
    pub fn write<'a, K: Token<Keyhole>>(&'a self, token: &'a mut K) -> &'a mut T {
        self.try_write(token).unwrap()
    }

    /// Get a reference to the contained data. Return `BadTokenError` if `token`
    /// doesn't fit in the [`keyhole`](TokenLock::keyhole).
    #[inline]
    pub fn try_read<'a, K: Token<Keyhole>>(&'a self, token: &'a K) -> Result<&'a T, BadTokenError> {
        if token.eq_id(&self.keyhole) {
            Ok(unsafe { &*self.data.get() })
        } else {
            Err(BadTokenError)
        }
    }

    /// Get a mutable reference to the contained data. Return `BadTokenError` if
    /// `token` doesn't fit in the [`keyhole`](TokenLock::keyhole).
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

impl<T, Keyhole> TokenLock<T, Keyhole> {
    /// Get the contained data by cloning. Panic if `token` doesn't fit in
    /// the [`keyhole`](TokenLock::keyhole).
    pub fn get<K: Token<Keyhole>>(&self, token: &K) -> T
    where
        T: Clone,
    {
        self.read(token).clone()
    }

    /// Get the contained data by cloning. Return `BadTokenError` if `token`
    /// doesn't fit in the [`keyhole`](TokenLock::keyhole).
    pub fn try_get<K: Token<Keyhole>>(&self, token: &K) -> Result<T, BadTokenError>
    where
        T: Clone,
    {
        Ok(self.try_read(token)?.clone())
    }

    /// Take the contained data, leaving `Default::default()` in its place.
    /// Panic if `token` doesn't fit in the [`keyhole`](TokenLock::keyhole).
    pub fn take<K: Token<Keyhole>>(&self, token: &mut K) -> T
    where
        T: Default,
    {
        self.replace_with(token, |_| Default::default())
    }

    /// Take the contained data, leaving `Default::default()` in its place.
    /// Return `BadTokenError` if `token` doesn't fit in the
    /// [`keyhole`](TokenLock::keyhole).
    pub fn try_take<K: Token<Keyhole>>(&self, token: &mut K) -> Result<T, BadTokenError>
    where
        T: Default,
    {
        self.try_replace_with(token, |_| Default::default())
    }

    /// Replace the contained data with a new one. Panic if `token` doesn't fit
    /// in the [`keyhole`](TokenLock::keyhole).
    ///
    /// This function corresponds to [`std::mem::replace`].
    pub fn replace<K: Token<Keyhole>>(&self, token: &mut K, t: T) -> T {
        std_core::mem::replace(self.write(token), t)
    }

    /// Replace the contained data with a new one computed by the given
    /// closure. Panic if `token` doesn't fit in the
    /// [`keyhole`](TokenLock::keyhole).
    ///
    /// This function corresponds to [`std::mem::replace`].
    pub fn replace_with<K: Token<Keyhole>>(&self, token: &mut K, f: impl FnOnce(&mut T) -> T) -> T {
        self.try_replace_with(token, f).unwrap()
    }

    /// Replace the contained data with a new one computed by `f`. Panic if
    /// `token` doesn't fit in the [`keyhole`](TokenLock::keyhole).
    ///
    /// This function corresponds to [`std::mem::replace`].
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
    /// `token` doesn't fit in the [`keyhole`](TokenLock::keyhole) of both
    /// `TokenLock`s.
    ///
    /// This function corresponds to [`std::mem::swap`].
    pub fn swap<IOther, K: Token<Keyhole> + Token<IOther>>(
        &self,
        token: &mut K,
        other: &TokenLock<T, IOther>,
    ) {
        self.try_swap(token, other).unwrap()
    }

    /// Swap the contained data with the contained data of `other`. Return
    /// `BadTokenError` if `token` doesn't fit in the
    /// [`keyhole`](TokenLock::keyhole) of both `TokenLock`s.
    pub fn try_swap<IOther, K: Token<Keyhole> + Token<IOther>>(
        &self,
        token: &mut K,
        other: &TokenLock<T, IOther>,
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

impl<T: Clone, Keyhole: Clone> TokenLock<T, Keyhole> {
    /// Clone the `TokenLock`. Panic if `token` doesn't fit in the
    /// [`keyhole`](TokenLock::keyhole).
    pub fn clone<K: Token<Keyhole>>(&self, token: &K) -> Self {
        let value = self.get(token);
        Self::new(self.keyhole.clone(), value)
    }

    /// Clone the `TokenLock`. Return `BadTokenError` if `token` doesn't fit in
    /// the [`keyhole`](TokenLock::keyhole).
    pub fn try_clone<K: Token<Keyhole>>(&self, token: &K) -> Result<Self, BadTokenError> {
        let value = self.try_get(token)?;
        Ok(Self::new(self.keyhole.clone(), value))
    }
}

#[test]
#[cfg(feature = "std")]
fn basic() {
    let mut token = ArcToken::new();
    let lock = TokenLock::new(token.id(), 1);
    assert_eq!(*lock.read(&token), 1);

    let guard = lock.write(&mut token);
    assert_eq!(*guard, 1);
}

#[test]
#[cfg(feature = "std")]
fn bad_token() {
    let token1 = ArcToken::new();
    let mut token2 = ArcToken::new();
    let lock = TokenLock::new(token1.id(), 1);
    assert_eq!(lock.try_write(&mut token2), Err(BadTokenError));
}
