use crate::std_core::{fmt, hash, marker::PhantomData, ops, ptr::NonNull};

use super::{Token, Unsync};

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
/// The second type parameter (`Variant`) is internal use only and exempt from
/// the API stability guarantee.
///
/// [`TokenLock`]: crate::TokenLock
///
/// # `Sync`-ness Conversion
///
/// `SingletonToken` can be converted back and forth to its non-`Sync`
/// variation, [`UnsyncSingletonToken`], by the following methods:
///
/// |         |        | To `Sync`            | To `!Sync`            |
/// | ------- | ------ | -------------------- | --------------------- |
/// | `Sync`  | `&mut` | [`borrow_mut`]       | [`borrow_unsync_mut`] |
/// |         | `&`    | [`borrow`]           | †                     |
/// |         | owned  |                      | [`into_unsync`]       |
/// | `!Sync` | `&mut` | [`borrow_sync_mut`]  | [`borrow_mut`]        |
/// |         | `&`    | [`borrow_sync`]      | [`borrow`]            |
/// |         | owned  | [`into_sync`]        |                       |
///
/// [`borrow_mut`]: SingletonToken::borrow_mut
/// [`borrow_unsync_mut`]: SingletonToken::borrow_unsync_mut
/// [`borrow`]: SingletonToken::borrow
/// [`borrow_sync_mut`]: SingletonToken::borrow_sync_mut
/// [`borrow_sync`]: SingletonToken::borrow_sync
/// [`into_unsync`]: SingletonToken::into_unsync
/// [`into_sync`]: SingletonToken::into_sync
///
/// † `borrow_unsync` doesn't exist because `&SingletonToken` (the `Sync`
/// variation) might already be owned by multiple threads, so converting them
/// to the `!Sync` variation would violate the `!Sync` requirement.
///
/// The non-`Sync` variation can be used to access the contents of
/// [`UnsyncTokenLock`].
///
/// [`UnsyncTokenLock`]: crate::UnsyncTokenLock
pub struct SingletonToken<Tag: ?Sized, Variant = SyncVariant>(
    PhantomData<(Invariant<Tag>, Variant)>,
);

/// The `!Sync` variant of [`SingletonToken`].
///
///
/// # Examples
///
/// ```
/// # use tokenlock::*;
/// use std::{cell::Cell, thread::spawn};
/// struct MyTag;
/// impl_singleton_token_factory!(MyTag);
///
/// type MyTokenLock<T> = UnsyncTokenLock<T, SingletonTokenId<MyTag>>;
/// type MyToken = UnsyncSingletonToken<MyTag>;
/// type MyTokenId = SingletonTokenId<MyTag>;
///
/// static LOCK1: MyTokenLock<Cell<u32>> =
///     MyTokenLock::new(MyTokenId::new(), Cell::new(1));
///
/// // Create a singleton token with a runtime uniqueness check
/// let mut token = MyToken::new().unwrap();
///
/// spawn(move || {
///     // Shared references can alias
///     let (token_1, token_2) = (token.borrow(), token.borrow());
///
///     LOCK1.read(&*token_1).set(2);
///     LOCK1.read(&*token_2).set(4);
/// });
/// ```
pub type UnsyncSingletonToken<Tag> = SingletonToken<Tag, UnsyncVariant>;

#[doc(hidden)]
pub struct SyncVariant(());
#[doc(hidden)]
pub struct UnsyncVariant(std::cell::Cell<()>);

#[doc(hidden)]
pub trait SingletonTokenVariant: private::Sealed {}
impl SingletonTokenVariant for SyncVariant {}
impl SingletonTokenVariant for UnsyncVariant {}

mod private {
    pub trait Sealed {}
    impl Sealed for super::SyncVariant {}
    impl Sealed for super::UnsyncVariant {}
}

// FIXME: Work-around for the construction of `PhantomData<fn(...)>` being
//        unstable <https://github.com/rust-lang/rust/issues/67649>
struct Invariant<Tag: ?Sized>(fn(&Tag) -> &Tag);

impl<Tag: ?Sized, Variant: SingletonTokenVariant> fmt::Debug for SingletonToken<Tag, Variant> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonToken")
    }
}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> PartialEq for SingletonToken<Tag, Variant> {
    #[inline]
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> Eq for SingletonToken<Tag, Variant> {}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> hash::Hash for SingletonToken<Tag, Variant> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}

impl<Tag: ?Sized, Variant> SingletonToken<Tag, Variant> {
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

    /// Borrow `self` as [`SingletonTokenRef`] or [`UnsyncSingletonTokenRef`]
    /// of the same `Sync`-ness as `Self`.
    ///
    /// `SingletonTokenRef` is truly zero-sized, so it's more efficient to
    /// store and pass than `&SingletonToken`.
    #[inline]
    pub fn borrow(&self) -> SingletonTokenRef<'_, Tag, Variant> {
        SingletonTokenRef(PhantomData)
    }

    /// Borrow `self` mutably as [`SingletonTokenRefMut`]
    /// or [`UnsyncSingletonTokenRefMut`] of the same `Sync`-ness as `Self`.
    ///
    /// `SingletonTokenRefMut` is truly zero-sized, so it's more efficient to
    /// store and pass than `&mut SingletonToken`.
    #[inline]
    pub fn borrow_mut(&mut self) -> SingletonTokenRefMut<'_, Tag, Variant> {
        SingletonTokenRefMut(PhantomData)
    }
}

impl<Tag: ?Sized> UnsyncSingletonToken<Tag> {
    /// Borrow `self: UnsyncSingletonToken` as [`SingletonTokenRef`].
    #[inline]
    pub fn borrow_sync(&self) -> SingletonTokenRef<'_, Tag> {
        SingletonTokenRef(PhantomData)
    }

    /// Borrow `self: UnsyncSingletonToken` mutably as [`SingletonTokenRefMut`].
    #[inline]
    pub fn borrow_sync_mut(&mut self) -> SingletonTokenRefMut<'_, Tag> {
        SingletonTokenRefMut(PhantomData)
    }
}

impl<Tag: ?Sized> SingletonToken<Tag> {
    /// Borrow `self: SingletonToken` mutably as [`UnsyncSingletonTokenRefMut`].
    ///
    /// There is no `borrow_unsync` because that would allow
    /// `UnsyncSingletonToken` to be logically borrowed by multiple threads.
    #[inline]
    pub fn borrow_unsync_mut(&mut self) -> UnsyncSingletonTokenRefMut<'_, Tag> {
        SingletonTokenRefMut(PhantomData)
    }
}

impl<Tag: ?Sized> SingletonToken<Tag> {
    /// Convert `SingletonToken` to the `!Sync` variant.
    #[inline]
    pub const fn into_unsync(self) -> UnsyncSingletonToken<Tag> {
        SingletonToken(PhantomData)
    }
}

impl<Tag: ?Sized> UnsyncSingletonToken<Tag> {
    /// Convert `UnsyncSingletonToken` to the `Sync` variant.
    #[inline]
    pub const fn into_sync(self) -> SingletonToken<Tag> {
        SingletonToken(PhantomData)
    }
}

unsafe impl<Tag: ?Sized, Variant: SingletonTokenVariant> Token<SingletonTokenId<Tag>>
    for SingletonToken<Tag, Variant>
{
    #[inline(always)]
    fn eq_id(&self, _: &SingletonTokenId<Tag>) -> bool {
        true
    }
}

unsafe impl<Tag: ?Sized> Unsync for UnsyncSingletonToken<Tag> {}

/// Zero-sized logical equivalent of `&'a `[`SingletonToken`]`<Tag>`.
///
/// The second type parameter (`Variant`) is internal use only and exempt from
/// the API stability guarantee.
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
///
/// `SingletonTokenRef` does not allow mutable borrow:
///
/// ```rust,compile_fail
/// # use tokenlock::*;
/// # struct MyTag;
/// # impl_singleton_token_factory!(MyTag);
/// # let token = SingletonToken::<MyTag>::new().unwrap();
/// # let lock = TokenLock::new(token.id(), 1);
/// let token_ref: SingletonTokenRef<MyTag> = token.borrow();
///
/// // compile error: `SingletonTokenRef` does not implement `DerefMut`
/// *lock.write(&mut *token_ref) = 4;
/// ```
///
/// `SingletonTokenRef` is `Send`-able because [`SingletonToken`] is `Sync`:
///
/// ```rust
/// # use tokenlock::*;
/// # struct MyTag;
/// # impl_singleton_token_factory!(MyTag);
/// let token: &'static SingletonTokenGuard<MyTag> =
///     Box::leak(Box::new(SingletonToken::<MyTag>::new().unwrap()));
/// let token_ref: SingletonTokenRef<MyTag> = token.borrow();
/// std::thread::spawn(move || {
///     let _token_ref = token_ref;
/// });
/// ```
pub struct SingletonTokenRef<'a, Tag: ?Sized, Variant = SyncVariant>(
    PhantomData<&'a SingletonToken<Tag, Variant>>,
);

/// Zero-sized logical equivalent of `&'a `[`UnsyncSingletonToken`]`<Tag>`. The
/// `!Sync` variant of [`SingletonTokenRef`].
///
/// # Examples
///
/// ```
/// # use tokenlock::*;
/// struct MyTag;
/// impl_singleton_token_factory!(MyTag);
/// let token = UnsyncSingletonToken::<MyTag>::new().unwrap();
/// let lock = UnsyncTokenLock::new(token.id(), 1);
///
/// // `UnsyncSingletonTokenRef` is zero-sized (unlike `&UnsyncSingletonToken`), so there is
/// // no runtime overhead involved with passing `UnsyncSingletonTokenRef`.
/// access_lock(token.borrow(), &lock);
///
/// fn access_lock(
///     token: UnsyncSingletonTokenRef<'_, MyTag>,
///     lock: &UnsyncTokenLock<u32, SingletonTokenId<MyTag>>,
/// ) {
///     assert_eq!(*lock.read(&*token), 1);
/// }
/// ```
///
/// `UnsyncSingletonTokenRef` does not allow mutable borrow:
///
/// ```rust,compile_fail
/// # use tokenlock::*;
/// # struct MyTag;
/// # impl_singleton_token_factory!(MyTag);
/// # let token = UnsyncSingletonToken::<MyTag>::new().unwrap();
/// # let lock = UnsyncTokenLock::new(token.id(), 1);
/// let token_ref: UnsyncSingletonTokenRef<MyTag> = token.borrow();
///
/// // compile error: `UnsyncSingletonTokenRef` does not implement `DerefMut`
/// *lock.write(&mut *token_ref) = 4;
/// ```
///
/// `UnsyncSingletonTokenRef` is not `Send`-able because
/// [`UnsyncSingletonToken`] is not `Sync`:
///
/// ```rust,compile_fail
/// # use tokenlock::*;
/// # struct MyTag;
/// # impl_singleton_token_factory!(MyTag);
/// let token: &'static UnsyncSingletonTokenGuard<MyTag> =
///     Box::leak(Box::new(UnsyncSingletonToken::<MyTag>::new().unwrap()));
/// let token_ref: UnsyncSingletonTokenRef<MyTag> = token.borrow();
/// // compile error: `UnsyncSingletonTokenRef` is not `Send`
/// std::thread::spawn(move || {
///     let _token_ref = token_ref;
/// });
/// ```
pub type UnsyncSingletonTokenRef<'a, Tag> = SingletonTokenRef<'a, Tag, UnsyncVariant>;

impl<Tag: ?Sized, Variant: SingletonTokenVariant> fmt::Debug
    for SingletonTokenRef<'_, Tag, Variant>
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonTokenRef")
    }
}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> PartialEq
    for SingletonTokenRef<'_, Tag, Variant>
{
    #[inline]
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> Eq for SingletonTokenRef<'_, Tag, Variant> {}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> hash::Hash
    for SingletonTokenRef<'_, Tag, Variant>
{
    #[inline]
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> ops::Deref
    for SingletonTokenRef<'_, Tag, Variant>
{
    type Target = SingletonToken<Tag, Variant>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &SingletonToken(PhantomData)
    }
}

/// Zero-sized logical equivalent of `&'a mut `[`SingletonToken`]`<Tag>`.
///
/// The second type parameter (`Variant`) is internal use only and exempt from
/// the API stability guarantee.
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
///
/// `SingletonTokenRefMut` is `Send`-able because [`SingletonToken`] is `Send`:
///
/// ```rust
/// # use tokenlock::*;
/// # struct MyTag;
/// # impl_singleton_token_factory!(MyTag);
/// let token: &'static mut SingletonTokenGuard<MyTag> =
///     Box::leak(Box::new(SingletonToken::<MyTag>::new().unwrap()));
/// let token_ref: SingletonTokenRefMut<MyTag> = token.borrow_mut();
/// std::thread::spawn(move || {
///     let _token_ref = token_ref;
/// });
/// ```
pub struct SingletonTokenRefMut<'a, Tag: ?Sized, Variant = SyncVariant>(
    PhantomData<&'a mut SingletonToken<Tag, Variant>>,
);

/// Zero-sized logical equivalent of `&'a mut `[`UnsyncSingletonToken`]`<Tag>`. The
/// `!Sync` variant of [`SingletonTokenRefMut`].
///
/// # Examples
///
/// `UnsyncSingletonTokenRefMut` is `Send`-able because [`UnsyncSingletonToken`]
/// is `Send`:
///
/// ```rust
/// # use tokenlock::*;
/// # struct MyTag;
/// # impl_singleton_token_factory!(MyTag);
/// let token: &'static mut UnsyncSingletonTokenGuard<MyTag> =
///     Box::leak(Box::new(UnsyncSingletonToken::<MyTag>::new().unwrap()));
/// let token_ref: UnsyncSingletonTokenRefMut<MyTag> = token.borrow_mut();
/// std::thread::spawn(move || {
///     let _token_ref = token_ref;
/// });
/// ```
pub type UnsyncSingletonTokenRefMut<'a, Tag> = SingletonTokenRefMut<'a, Tag, UnsyncVariant>;

impl<Tag: ?Sized, Variant: SingletonTokenVariant> fmt::Debug
    for SingletonTokenRefMut<'_, Tag, Variant>
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonTokenRefMut")
    }
}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> PartialEq
    for SingletonTokenRefMut<'_, Tag, Variant>
{
    #[inline]
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> Eq for SingletonTokenRefMut<'_, Tag, Variant> {}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> hash::Hash
    for SingletonTokenRefMut<'_, Tag, Variant>
{
    #[inline]
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> ops::Deref
    for SingletonTokenRefMut<'_, Tag, Variant>
{
    type Target = SingletonToken<Tag>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &SingletonToken(PhantomData)
    }
}

impl<Tag: ?Sized, Variant: SingletonTokenVariant> ops::DerefMut
    for SingletonTokenRefMut<'_, Tag, Variant>
{
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
    #[inline]
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<Tag: ?Sized> Default for SingletonTokenId<Tag> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<Tag: ?Sized> fmt::Debug for SingletonTokenId<Tag> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("SingletonTokenId")
    }
}

impl<Tag: ?Sized> Clone for SingletonTokenId<Tag> {
    #[inline]
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<Tag: ?Sized> Copy for SingletonTokenId<Tag> {}

impl<Tag: ?Sized> PartialEq for SingletonTokenId<Tag> {
    #[inline]
    fn eq(&self, _: &Self) -> bool {
        false
    }
}

impl<Tag: ?Sized> Eq for SingletonTokenId<Tag> {}

impl<Tag: ?Sized> hash::Hash for SingletonTokenId<Tag> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, _: &mut H) {}
}
