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
//! inforgeable token.
//!
//! # Examples
//!
//! ```
//! # use tokenlock::*;
//! let mut token = Token::new();
//!
//! let lock = TokenLock::new(&token, 1);
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
//! # let mut token = Token::new();
//! let lock = Arc::new(TokenLock::new(&token, 1));
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
//! let mut token = Token::new();
//! let lock = TokenLock::new(&token, 1);
//! let guard = lock.write(&mut token).unwrap();
//! drop(lock); // compile error: `guard` cannot outlive `TokenLock`
//! ```
//!
//! ```compile_fail
//! # use tokenlock::*;
//! # use std::mem::drop;
//! # let mut token = Token::new();
//! # let lock = TokenLock::new(&token, 1);
//! # let guard = lock.write(&mut token).unwrap();
//! drop(token); // compile error: `guard` cannot outlive `Token`
//! ```
//!
//! It also prevents from forming a reference to the contained value when
//! there already is a mutable reference to it:
//!
//! ```compile_fail
//! # use tokenlock::*;
//! # let mut token = Token::new();
//! # let lock = TokenLock::new(&token, 1);
//! let write_guard = lock.write(&mut token).unwrap();
//! let read_guard = lock.read(&token).unwrap(); // compile error
//! ```
//!
//! While allowing multiple immutable references:
//!
//! ```
//! # use tokenlock::*;
//! # let mut token = Token::new();
//! # let lock = TokenLock::new(&token, 1);
//! let read_guard1 = lock.read(&token).unwrap();
//! let read_guard2 = lock.read(&token).unwrap();
//! ```
use std::{fmt, hash};
use std::cell::UnsafeCell;
use std::sync::Arc;

/// An inforgeable token used to access the contents of a `TokenLock`.
///
/// This type is not `Clone` to ensure an exclusive access to `TokenLock`.
///
/// See the [module-level documentation] for more details.
///
/// [module-level documentation]: index.html
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Token(UniqueId);

unsafe impl Send for Token {}
unsafe impl Sync for Token {}

impl Token {
    pub fn new() -> Self {
        Token(UniqueId::new())
    }
}

impl Default for Token {
    fn default() -> Self {
        Self::new()
    }
}

/// Token that cannot be used to access the contents of a `TokenLock`, but can
/// be used to create a new `TokenLock`.
///
/// See the [module-level documentation] for more details.
///
/// [module-level documentation]: index.html
///
/// # Examples
///
/// The parameter of `TokenLock::new` accepts `Into<TokenRef>`, so the following
/// codes are equivalent:
///
/// ```
/// # use tokenlock::*;
/// # let mut token = Token::new();
/// TokenLock::new(&token, 1);
/// TokenLock::new(TokenRef::from(&token), 1);
/// ```
///
/// `TokenRef` can be cloned while `Token` cannot:
///
/// ```
/// # use tokenlock::*;
/// let mut token = Token::new();
/// let token_ref = TokenRef::from(&token);
/// let lock1 = TokenLock::new(token_ref.clone(), 1);
/// let lock2 = TokenLock::new(token_ref.clone(), 2);
/// ```
///
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct TokenRef(UniqueId);

impl<'a> From<&'a Token> for TokenRef {
    fn from(x: &'a Token) -> TokenRef {
        TokenRef(x.0.clone())
    }
}

/// A mutual exclusive primitive that can be accessed using a `Token`
/// with a very low over-head.
///
/// See the [module-level documentation] for more details.
///
/// [module-level documentation]: index.html
pub struct TokenLock<T: ?Sized> {
    keyhole: UniqueId,
    data: UnsafeCell<T>,
}

unsafe impl<T: ?Sized + Send + Sync> Send for TokenLock<T> {}
unsafe impl<T: ?Sized + Send + Sync> Sync for TokenLock<T> {}

impl<T: ?Sized> fmt::Debug for TokenLock<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("TokenLock")
            .field("keyhole", &self.keyhole)
            .finish()
    }
}

impl<T> TokenLock<T> {
    pub fn new<S: Into<TokenRef>>(token: S, data: T) -> Self {
        Self {
            keyhole: token.into().0,
            data: UnsafeCell::new(data),
        }
    }
}

impl<T: ?Sized> TokenLock<T> {
    #[inline]
    #[allow(dead_code)]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data.get() }
    }

    #[inline]
    #[allow(dead_code)]
    pub fn read<'a>(&'a self, token: &'a Token) -> Option<&'a T> {
        if token.0 == self.keyhole {
            Some(unsafe { &*self.data.get() })
        } else {
            None
        }
    }

    #[inline]
    pub fn write<'a>(&'a self, token: &'a mut Token) -> Option<&'a mut T> {
        if token.0 == self.keyhole {
            Some(unsafe { &mut *self.data.get() })
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
struct UniqueId(Arc<usize>);

impl PartialEq for UniqueId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for UniqueId {}

impl hash::Hash for UniqueId {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        (*self.0).hash(state)
    }
}

impl UniqueId {
    pub fn new() -> Self {
        // This guarantees consistent hash generation even if Rust would
        // implement a moving GC in future
        let mut arc = Arc::new(0);
        let id = &*arc as *const usize as usize;
        *Arc::get_mut(&mut arc).unwrap() = id;
        UniqueId(arc)
    }
}

#[test]
fn basic() {
    let mut token = Token::new();
    let lock = TokenLock::new(&token, 1);
    assert_eq!(*lock.read(&token).unwrap(), 1);

    let guard = lock.write(&mut token).unwrap();
    assert_eq!(*guard, 1);
}

#[test]
fn bad_token() {
    let token1 = Token::new();
    let mut token2 = Token::new();
    let lock = TokenLock::new(&token1, 1);
    assert!(lock.write(&mut token2).is_none());
}
