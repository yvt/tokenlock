use crate::std_core::{fmt, hash, marker::PhantomData};

use super::Token;

/// A singleton unforgeable token used to access the contents of a
/// `TokenLock`.
///
/// It's a singleton object, meaning there can be only one instance of
/// `SingletonToken<T>` for each specific `T`. The instances of `SingletonToken`
/// are solely distinguished by its type parameter, making this type zero-sized.
///
/// This type lacks a `Clone` implementation to ensure exclusive access to
/// [`TokenLock`].
///
/// This type is invariant over `T`.
///
/// [`TokenLock`]: crate::TokenLock
pub struct SingletonToken<T: ?Sized>(PhantomData<fn(T) -> T>);

impl<T: ?Sized> fmt::Debug for SingletonToken<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonToken")
    }
}

impl<T: ?Sized> PartialEq for SingletonToken<T> {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<T: ?Sized> Eq for SingletonToken<T> {}

impl<T: ?Sized> hash::Hash for SingletonToken<T> {
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}

impl<T: ?Sized> SingletonToken<T> {
    /// Construct `Self` without checking the singleton invariant.
    ///
    /// # Safety
    ///
    /// Having more than one instance of `SingletonToken<T>` for a
    /// particular `T` violates [`Token`]'s requirements and allows a
    /// `TokenLock` to be mutably borrowed simultaneously, violating the pointer
    /// aliasing rules.
    #[inline(always)]
    pub unsafe fn new_unchecked() -> Self {
        Self(PhantomData)
    }

    /// Construct an [`SingletonTokenId`] that equates to `self`.
    #[inline(always)]
    pub fn id(&self) -> SingletonTokenId<T> {
        SingletonTokenId(PhantomData)
    }
}

unsafe impl<T: ?Sized> Token<SingletonTokenId<T>> for SingletonToken<T> {
    #[inline(always)]
    fn eq_id(&self, _: &SingletonTokenId<T>) -> bool {
        true
    }
}

/// Token that cannot be used to access the contents of a [`TokenLock`], but can
/// be used to create a new `TokenLock`.
///
/// [`TokenLock`]: crate::TokenLock
///
/// This type is invariant over `T`.
///
/// # Examples
///
/// `SingletonTokenId` can be cloned while [`SingletonToken`] cannot:
///
/// ```
/// # use tokenlock::*;
/// let token = unsafe { SingletonToken::<u32>::new_unchecked() };
/// let token_id = token.id();
/// let lock1 = TokenLock::new(token_id.clone(), 1);
/// let lock2 = TokenLock::new(token_id, 2);
/// ```
///
pub struct SingletonTokenId<T: ?Sized>(PhantomData<fn(T) -> T>);

impl<T: ?Sized> fmt::Debug for SingletonTokenId<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonTokenId")
    }
}

impl<T: ?Sized> Clone for SingletonTokenId<T> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<T: ?Sized> Copy for SingletonTokenId<T> {}

impl<T: ?Sized> PartialEq for SingletonTokenId<T> {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<T: ?Sized> Eq for SingletonTokenId<T> {}

impl<T: ?Sized> hash::Hash for SingletonTokenId<T> {
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}
