use crate::std_core::{fmt, hash, marker::PhantomData, ops, ptr::NonNull};

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
pub struct SingletonToken<T: ?Sized>(PhantomData<Invariant<T>>);

// FIXME: Work-around for the construction of `PhantomData<fn(...)>` being
//        unstable <https://github.com/rust-lang/rust/issues/67649>
struct Invariant<T: ?Sized>(fn(&T) -> &T);

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
    pub const unsafe fn new_unchecked() -> Self {
        Self(PhantomData)
    }

    /// Construct an [`SingletonTokenId`] that equates to `self`.
    #[inline(always)]
    pub fn id(&self) -> SingletonTokenId<T> {
        SingletonTokenId(PhantomData)
    }

    /// Borrow `self` as [`SingletonTokenRef`].
    ///
    /// `SingletonTokenRef` is truly zero-sized, so it's more efficient to
    /// store and pass than `&SingletonToken`.
    pub fn borrow(&self) -> SingletonTokenRef<'_, T> {
        SingletonTokenRef(PhantomData)
    }

    /// Borrow `self` mutably as [`SingletonTokenRefMut`].
    ///
    /// `SingletonTokenRefMut` is truly zero-sized, so it's more efficient to
    /// store and pass than `&mut SingletonToken`.
    pub fn borrow_mut(&mut self) -> SingletonTokenRefMut<'_, T> {
        SingletonTokenRefMut(PhantomData)
    }
}

unsafe impl<T: ?Sized> Token<SingletonTokenId<T>> for SingletonToken<T> {
    #[inline(always)]
    fn eq_id(&self, _: &SingletonTokenId<T>) -> bool {
        true
    }
}

/// Zero-sized logical equivalent of `&'a `[`SingletonToken`]`<T>`.
///
/// # Examples
///
/// ```
/// # use tokenlock::*;
/// struct MyTag;
/// impl_singleton_token_factory!(MyTag);
/// let token = SingletonToken::<MyTag>::new().unwrap();
/// let lock = TokenLock::new(token.id(), 1);
///
/// // `SingletonTokenRef` is zero-sized (unlike `&SingletonToken`), so there is
/// // no runtime overhead involved with passing `SingletonTokenRef`.
/// access_lock(token.borrow(), &lock);
///
/// fn access_lock(
///     token: SingletonTokenRef<'_, MyTag>,
///     lock: &TokenLock<u32, SingletonTokenId<MyTag>>,
/// ) {
///     assert_eq!(*lock.read(&*token), 1);
/// }
/// ```
pub struct SingletonTokenRef<'a, T: ?Sized>(PhantomData<&'a SingletonToken<T>>);

impl<T: ?Sized> fmt::Debug for SingletonTokenRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonTokenRef")
    }
}

impl<T: ?Sized> PartialEq for SingletonTokenRef<'_, T> {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<T: ?Sized> Eq for SingletonTokenRef<'_, T> {}

impl<T: ?Sized> hash::Hash for SingletonTokenRef<'_, T> {
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}

impl<T: ?Sized> ops::Deref for SingletonTokenRef<'_, T> {
    type Target = SingletonToken<T>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &SingletonToken(PhantomData)
    }
}

/// Zero-sized logical equivalent of `&'a mut `[`SingletonToken`]`<T>`.
///
/// # Examples
///
/// ```
/// # use tokenlock::*;
/// struct MyTag;
/// impl_singleton_token_factory!(MyTag);
/// let mut token = SingletonToken::<MyTag>::new().unwrap();
/// let lock = TokenLock::new(token.id(), 1);
///
/// // `SingletonTokenRefMut` is zero-sized (unlike `&SingletonToken`), so there is
/// // no runtime overhead involved with passing `SingletonTokenRefMut`.
/// access_lock(token.borrow_mut(), &lock);
///
/// fn access_lock(
///     mut token: SingletonTokenRefMut<'_, MyTag>,
///     lock: &TokenLock<u32, SingletonTokenId<MyTag>>,
/// ) {
///     assert_eq!(*lock.read(&*token), 1);
///     lock.replace(&mut *token, 2);
/// }
/// ```
pub struct SingletonTokenRefMut<'a, T: ?Sized>(PhantomData<&'a mut SingletonToken<T>>);

impl<T: ?Sized> fmt::Debug for SingletonTokenRefMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonTokenRefMut")
    }
}

impl<T: ?Sized> PartialEq for SingletonTokenRefMut<'_, T> {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<T: ?Sized> Eq for SingletonTokenRefMut<'_, T> {}

impl<T: ?Sized> hash::Hash for SingletonTokenRefMut<'_, T> {
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}

impl<T: ?Sized> ops::Deref for SingletonTokenRefMut<'_, T> {
    type Target = SingletonToken<T>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &SingletonToken(PhantomData)
    }
}

impl<T: ?Sized> ops::DerefMut for SingletonTokenRefMut<'_, T> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        // Logically borrow the original `SingletonToken`
        // Safety: `Self` is zero-sized, so the returned reference does not
        //         point to an invalid memory region.
        unsafe { &mut *NonNull::dangling().as_ptr() }
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
/// struct MyTag;
/// impl_singleton_token_factory!(MyTag);
/// let token = SingletonToken::<MyTag>::new().unwrap();
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
