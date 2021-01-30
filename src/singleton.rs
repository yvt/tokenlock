use crate::std_core::{fmt, hash, marker::PhantomData, ops, ptr::NonNull};

use super::Token;

/// A singleton unforgeable token used to access the contents of a
/// `TokenLock`.
///
/// It's a singleton object, meaning there can be only one instance of
/// `SingletonToken<Tag>` for each specific `Tag`. The instances of
/// `SingletonToken` are solely distinguished by its type parameter `Tag`,
/// making this type zero-sized.
///
/// This type lacks a `Clone` implementation to ensure exclusive access to
/// [`TokenLock`].
///
/// This type is invariant over `Tag`.
///
/// [`TokenLock`]: crate::TokenLock
pub struct SingletonToken<Tag: ?Sized>(PhantomData<Invariant<Tag>>);

// FIXME: Work-around for the construction of `PhantomData<fn(...)>` being
//        unstable <https://github.com/rust-lang/rust/issues/67649>
struct Invariant<Tag: ?Sized>(fn(&Tag) -> &Tag);

impl<Tag: ?Sized> fmt::Debug for SingletonToken<Tag> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonToken")
    }
}

impl<Tag: ?Sized> PartialEq for SingletonToken<Tag> {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<Tag: ?Sized> Eq for SingletonToken<Tag> {}

impl<Tag: ?Sized> hash::Hash for SingletonToken<Tag> {
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}

impl<Tag: ?Sized> SingletonToken<Tag> {
    /// Construct `Self` without checking the singleton invariant.
    ///
    /// # Safety
    ///
    /// Having more than one instance of `SingletonToken<Tag>` for a
    /// particular `Tag` violates [`Token`]'s requirements and allows a
    /// `TokenLock` to be mutably borrowed simultaneously, violating the pointer
    /// aliasing rules.
    #[inline(always)]
    pub const unsafe fn new_unchecked() -> Self {
        Self(PhantomData)
    }

    /// Construct an [`SingletonTokenId`] that equates to `self`.
    #[inline(always)]
    pub fn id(&self) -> SingletonTokenId<Tag> {
        SingletonTokenId(PhantomData)
    }

    /// Borrow `self` as [`SingletonTokenRef`].
    ///
    /// `SingletonTokenRef` is truly zero-sized, so it's more efficient to
    /// store and pass than `&SingletonToken`.
    pub fn borrow(&self) -> SingletonTokenRef<'_, Tag> {
        SingletonTokenRef(PhantomData)
    }

    /// Borrow `self` mutably as [`SingletonTokenRefMut`].
    ///
    /// `SingletonTokenRefMut` is truly zero-sized, so it's more efficient to
    /// store and pass than `&mut SingletonToken`.
    pub fn borrow_mut(&mut self) -> SingletonTokenRefMut<'_, Tag> {
        SingletonTokenRefMut(PhantomData)
    }
}

unsafe impl<Tag: ?Sized> Token<SingletonTokenId<Tag>> for SingletonToken<Tag> {
    #[inline(always)]
    fn eq_id(&self, _: &SingletonTokenId<Tag>) -> bool {
        true
    }
}

/// Zero-sized logical equivalent of `&'a `[`SingletonToken`]`<Tag>`.
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
pub struct SingletonTokenRef<'a, Tag: ?Sized>(PhantomData<&'a SingletonToken<Tag>>);

impl<Tag: ?Sized> fmt::Debug for SingletonTokenRef<'_, Tag> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonTokenRef")
    }
}

impl<Tag: ?Sized> PartialEq for SingletonTokenRef<'_, Tag> {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<Tag: ?Sized> Eq for SingletonTokenRef<'_, Tag> {}

impl<Tag: ?Sized> hash::Hash for SingletonTokenRef<'_, Tag> {
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}

impl<Tag: ?Sized> ops::Deref for SingletonTokenRef<'_, Tag> {
    type Target = SingletonToken<Tag>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &SingletonToken(PhantomData)
    }
}

/// Zero-sized logical equivalent of `&'a mut `[`SingletonToken`]`<Tag>`.
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
pub struct SingletonTokenRefMut<'a, Tag: ?Sized>(PhantomData<&'a mut SingletonToken<Tag>>);

impl<Tag: ?Sized> fmt::Debug for SingletonTokenRefMut<'_, Tag> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonTokenRefMut")
    }
}

impl<Tag: ?Sized> PartialEq for SingletonTokenRefMut<'_, Tag> {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<Tag: ?Sized> Eq for SingletonTokenRefMut<'_, Tag> {}

impl<Tag: ?Sized> hash::Hash for SingletonTokenRefMut<'_, Tag> {
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}

impl<Tag: ?Sized> ops::Deref for SingletonTokenRefMut<'_, Tag> {
    type Target = SingletonToken<Tag>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &SingletonToken(PhantomData)
    }
}

impl<Tag: ?Sized> ops::DerefMut for SingletonTokenRefMut<'_, Tag> {
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
/// This type is invariant over `Tag`.
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
/// Unlike other token types, you don't need to construct `SingletonToken`
/// first, actually:
///
/// ```
/// # use tokenlock::*;
/// struct MyTag;
/// impl_singleton_token_factory!(MyTag);
/// let lock1 = TokenLock::new(SingletonTokenId::<MyTag>::new(), 1);
/// let lock2 = TokenLock::new(SingletonTokenId::<MyTag>::new(), 2);
/// ```
pub struct SingletonTokenId<Tag: ?Sized>(PhantomData<Invariant<Tag>>);

impl<Tag: ?Sized> SingletonTokenId<Tag> {
    /// Construct `Self`.
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<Tag: ?Sized> Default for SingletonTokenId<Tag> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Tag: ?Sized> fmt::Debug for SingletonTokenId<Tag> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonTokenId")
    }
}

impl<Tag: ?Sized> Clone for SingletonTokenId<Tag> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<Tag: ?Sized> Copy for SingletonTokenId<Tag> {}

impl<Tag: ?Sized> PartialEq for SingletonTokenId<Tag> {
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<Tag: ?Sized> Eq for SingletonTokenId<Tag> {}

impl<Tag: ?Sized> hash::Hash for SingletonTokenId<Tag> {
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}
