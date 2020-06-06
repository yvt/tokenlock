//
// Copyright 2020 yvt, all rights reserved.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//
//! Provides a `Send`-able cell type whose contents can be accessed only via an
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
//! `TokenLock` implements `Send` and `Sync` so it can be shared between threads,
//! but only the thread holding the original `Token` can access its contents.
//! `Token` cannot be cloned:
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
use core as std_core;
#[cfg(feature = "std")]
use std as std_core;

use self::std_core::cell::UnsafeCell;
use self::std_core::fmt;

#[cfg(feature = "std")]
mod arc;
#[cfg(feature = "std")]
mod rc;
#[cfg(feature = "std")]
pub use self::{arc::*, rc::*};

/// Trait for an unforgeable token used to access the contents of a
/// [`TokenLock`].
///
/// # Safety
///
/// Given two distinct instances of `T: Token` `x` and `y`,
/// `x.eq_id(i) && y.eq_id(i)` must not be `true` for any `i`.
pub unsafe trait Token<I> {
    fn eq_id(&self, id: &I) -> bool;
}

/// A mutual exclusive primitive that can be accessed using a [`Token`]`<I>`
/// with a very low over-head.
///
/// See the [module-level documentation] for more details.
///
/// [module-level documentation]: index.html
#[derive(Default)]
pub struct TokenLock<T: ?Sized, I> {
    keyhole: I,
    data: UnsafeCell<T>,
}

unsafe impl<T: ?Sized + Send + Sync, I: Send> Send for TokenLock<T, I> {}
unsafe impl<T: ?Sized + Send + Sync, I: Sync> Sync for TokenLock<T, I> {}

impl<T: ?Sized, I: fmt::Debug> fmt::Debug for TokenLock<T, I> {
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

impl<T, I> TokenLock<T, I> {
    pub const fn new(keyhole: I, data: T) -> Self {
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

impl<T: ?Sized, I> TokenLock<T, I> {
    #[inline]
    pub const fn keyhole(&self) -> &I {
        &self.keyhole
    }

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
    pub fn read<'a, K: Token<I>>(&'a self, token: &'a K) -> &'a T {
        self.try_read(token).unwrap()
    }

    /// Get a mutable reference to the contained data. Panic if `token` doesn't
    /// fit in the [`keyhole`](TokenLock::keyhole).
    #[inline]
    pub fn write<'a, K: Token<I>>(&'a self, token: &'a mut K) -> &'a mut T {
        self.try_write(token).unwrap()
    }

    /// Get a reference to the contained data. Return `BadTokenError` if `token`
    /// doesn't fit in the [`keyhole`](TokenLock::keyhole).
    #[inline]
    pub fn try_read<'a, K: Token<I>>(&'a self, token: &'a K) -> Result<&'a T, BadTokenError> {
        if token.eq_id(&self.keyhole) {
            Ok(unsafe { &*self.data.get() })
        } else {
            Err(BadTokenError)
        }
    }

    /// Get a mutable reference to the contained data. Return `BadTokenError` if
    /// `token` doesn't fit in the [`keyhole`](TokenLock::keyhole).
    #[inline]
    pub fn try_write<'a, K: Token<I>>(
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

impl<T, I> TokenLock<T, I> {
    /// Get the contained data by cloning. Panic if `token` doesn't fit in
    /// the [`keyhole`](TokenLock::keyhole).
    pub fn get<K: Token<I>>(&self, token: &K) -> T
    where
        T: Clone,
    {
        self.read(token).clone()
    }

    /// Get the contained data by cloning. Return `BadTokenError` if `token`
    /// doesn't fit in the [`keyhole`](TokenLock::keyhole).
    pub fn try_get<K: Token<I>>(&self, token: &K) -> Result<T, BadTokenError>
    where
        T: Clone,
    {
        Ok(self.try_read(token)?.clone())
    }

    /// Take the contained data, leaving `Default::default()` in its place.
    /// Panic if `token` doesn't fit in the [`keyhole`](TokenLock::keyhole).
    pub fn take<K: Token<I>>(&self, token: &mut K) -> T
    where
        T: Default,
    {
        self.replace_with(token, |_| Default::default())
    }

    /// Take the contained data, leaving `Default::default()` in its place.
    /// Return `BadTokenError` if `token` doesn't fit in the
    /// [`keyhole`](TokenLock::keyhole).
    pub fn try_take<K: Token<I>>(&self, token: &mut K) -> Result<T, BadTokenError>
    where
        T: Default,
    {
        self.try_replace_with(token, |_| Default::default())
    }

    /// Replace the contained data with a new one. Panic if `token` doesn't fit
    /// in the [`keyhole`](TokenLock::keyhole).
    ///
    /// This function corresponds to [`std::mem::replace`].
    pub fn replace<K: Token<I>>(&self, token: &mut K, t: T) -> T {
        std_core::mem::replace(self.write(token), t)
    }

    /// Replace the contained data with a new one computed by the given
    /// closure. Panic if `token` doesn't fit in the
    /// [`keyhole`](TokenLock::keyhole).
    ///
    /// This function corresponds to [`std::mem::replace`].
    pub fn replace_with<K: Token<I>>(&self, token: &mut K, f: impl FnOnce(&mut T) -> T) -> T {
        self.try_replace_with(token, f).unwrap()
    }

    /// Replace the contained data with a new one computed by `f`. Panic if
    /// `token` doesn't fit in the [`keyhole`](TokenLock::keyhole).
    ///
    /// This function corresponds to [`std::mem::replace`].
    pub fn try_replace_with<K: Token<I>>(
        &self,
        token: &mut K,
        f: impl FnOnce(&mut T) -> T,
    ) -> Result<T, BadTokenError> {
        let inner = self.try_write(token)?;
        let new = f(inner);
        Ok(std_core::mem::replace(inner, new))
    }

    /// Swap the contained data with the contained data of `other`. Panic if
    /// `token` doesn't fit in the [`keyhole`](TokenLock::keyhole).
    ///
    /// This function corresponds to [`std::mem::swap`].
    pub fn swap<IOther, K: Token<I> + Token<IOther>>(
        &self,
        token: &mut K,
        other: &TokenLock<T, IOther>,
    ) {
        self.try_swap(token, other).unwrap()
    }

    /// Swap the contained data with the contained data of `other`. Return
    /// `BadTokenError` if `token` doesn't fit in the
    /// [`keyhole`](TokenLock::keyhole) of both `TokenLock`s.
    pub fn try_swap<IOther, K: Token<I> + Token<IOther>>(
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

impl<T: Clone, I: Clone> TokenLock<T, I> {
    /// Clone the `TokenLock`. Panic if `token` doesn't fit in the
    /// [`keyhole`](TokenLock::keyhole).
    pub fn clone<K: Token<I>>(&self, token: &K) -> Self {
        let value = self.get(token);
        Self::new(self.keyhole.clone(), value)
    }

    /// Clone the `TokenLock`. Return `BadTokenError` if `token` doesn't fit in
    /// the [`keyhole`](TokenLock::keyhole).
    pub fn try_clone<K: Token<I>>(&self, token: &K) -> Result<Self, BadTokenError> {
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
