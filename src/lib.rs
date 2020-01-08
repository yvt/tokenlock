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
//! assert_eq!(*lock.read(&token).unwrap(), 1);
//!
//! let mut guard = lock.write(&mut token).unwrap();
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
//!     lock_1.write(&mut token_1).unwrap();
//! }).unwrap();
//!
//! // can't access the contents; I no longer have `Token`
//! // lock.write(&mut token).unwrap();
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
//! let guard = lock.write(&mut token).unwrap();
//! drop(lock); // compile error: `guard` cannot outlive `TokenLock`
//! drop(guard);
//! ```
//!
//! ```compile_fail
//! # use tokenlock::*;
//! # use std::mem::drop;
//! # let mut token = ArcToken::new();
//! # let lock = TokenLock::new(token.id(), 1);
//! # let guard = lock.write(&mut token).unwrap();
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
//! let write_guard = lock.write(&mut token).unwrap();
//! let read_guard = lock.read(&token).unwrap(); // compile error
//! drop(write_guard);
//! ```
//!
//! While allowing multiple immutable references:
//!
//! ```
//! # use tokenlock::*;
//! # let mut token = ArcToken::new();
//! # let lock = TokenLock::new(token.id(), 1);
//! let read_guard1 = lock.read(&token).unwrap();
//! let read_guard2 = lock.read(&token).unwrap();
//! ```
use std::cell::UnsafeCell;
use std::fmt;

mod arc;
mod rc;
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

impl<T, I> TokenLock<T, I> {
    pub fn new(keyhole: I, data: T) -> Self {
        Self {
            keyhole,
            data: UnsafeCell::new(data),
        }
    }
}

impl<T: ?Sized, I> TokenLock<T, I> {
    #[inline]
    pub fn keyhole(&self) -> &I {
        &self.keyhole
    }

    #[inline]
    #[allow(dead_code)]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data.get() }
    }

    #[inline]
    #[allow(dead_code)]
    pub fn read<'a, K: Token<I>>(&'a self, token: &'a K) -> Option<&'a T> {
        if token.eq_id(&self.keyhole) {
            Some(unsafe { &*self.data.get() })
        } else {
            None
        }
    }

    #[inline]
    pub fn write<'a, K: Token<I>>(&'a self, token: &'a mut K) -> Option<&'a mut T> {
        if token.eq_id(&self.keyhole) {
            Some(unsafe { &mut *self.data.get() })
        } else {
            None
        }
    }
}

#[test]
fn basic() {
    let mut token = ArcToken::new();
    let lock = TokenLock::new(token.id(), 1);
    assert_eq!(*lock.read(&token).unwrap(), 1);

    let guard = lock.write(&mut token).unwrap();
    assert_eq!(*guard, 1);
}

#[test]
fn bad_token() {
    let token1 = ArcToken::new();
    let mut token2 = ArcToken::new();
    let lock = TokenLock::new(token1.id(), 1);
    assert!(lock.write(&mut token2).is_none());
}
