use core::{fmt, mem, ops};

use crate::singleton::{SingletonToken, SingletonTokenVariant, SyncVariant, UnsyncVariant};

/// The RAII guard for a [`SingletonToken`] obtained through
/// [`SingletonToken::new`]. Returns the token to the factory automatically
/// when dropped.
///
/// The second type parameter (`Variant`) is internal use only and exempt from
/// the API stability guarantee.
pub struct SingletonTokenGuard<Tag: ?Sized + SingletonTokenFactory, Variant = SyncVariant> {
    token: SingletonToken<Tag, Variant>,
}

/// The `!Sync` variant of [`SingletonTokenGuard`].
pub type UnsyncSingletonTokenGuard<Tag> = SingletonTokenGuard<Tag, UnsyncVariant>;

/// Associates a type with a flag indicating whether an instance of
/// [`SingletonToken`]`<Self>` is present.
///
/// Enables the [`SingletonToken`]`::<Self>::`[`new`] method.
///
/// Use [`impl_singleton_token_factory!`] to implement this trait.
///
/// # Safety
///
/// Implementing this trait incorrectly might break [`Token`]'s invariants.
///
/// [`Token`]: crate::Token
/// [`new`]: SingletonToken::new
pub unsafe trait SingletonTokenFactory {
    /// Take a token. Returns `true` if successful.
    fn take() -> bool;
    /// Return a token.
    ///
    /// # Safety
    ///
    /// Each call to this method must be accompanied with the destruction of an
    /// actually-existing instance of `SingletonToken`.
    unsafe fn r#return();
}

/// Implement [`SingletonTokenFactory`] on given types.
///
/// The generated implementation uses `AtomicBool` and therefore might not
/// compile on some targets.
///
/// See [`SingletonToken::new`] for an example.
#[cfg(any(
    all(compiler_has_cfg_target_has_atomic, target_has_atomic = "8"),
    not(compiler_has_cfg_target_has_atomic)
))]
#[cfg_attr(feature = "doc_cfg", doc(cfg(target_has_atomic = "8")))]
#[macro_export]
macro_rules! impl_singleton_token_factory {
    ($($ty:ty),* $(,)*) => {$(
        impl $crate::SingletonTokenFactoryStorage for $ty {
            #[inline]
            unsafe fn __stfs_token_issued() -> &'static $crate::core::sync::atomic::AtomicBool {
                // The initialization by `false` (instead of `true`) ensures
                // that the variable is placed in `.bss`, not `.data`.
                static TOKEN_ISSUED: $crate::core::sync::atomic::AtomicBool =
                    $crate::core::sync::atomic::AtomicBool::new(false);
                &TOKEN_ISSUED
            }
        }

        unsafe impl $crate::SingletonTokenFactory for $ty {
            #[inline]
            fn take() -> $crate::core::primitive::bool {
                let token_issued =
                    unsafe { <$ty as $crate::SingletonTokenFactoryStorage>::__stfs_token_issued() };
                !token_issued.swap(true, $crate::core::sync::atomic::Ordering::Acquire)
            }
            // The inner `unsafe` block is redundant only if `unsafe_op_in_unsafe_fn`
            // (https://github.com/rust-lang/rust/issues/71668) is set to "allow".
            #[allow(unused_unsafe)]
            #[inline]
            unsafe fn r#return() {
                let token_issued =
                    unsafe { <$ty as $crate::SingletonTokenFactoryStorage>::__stfs_token_issued() };
                token_issued.store(false, $crate::core::sync::atomic::Ordering::Release);
            }
        }
    )*};
}

/// Internal use only
#[doc(hidden)]
#[cfg(any(
    all(compiler_has_cfg_target_has_atomic, target_has_atomic = "8"),
    not(compiler_has_cfg_target_has_atomic)
))]
pub trait SingletonTokenFactoryStorage {
    unsafe fn __stfs_token_issued() -> &'static core::sync::atomic::AtomicBool;
}

impl<Tag: ?Sized + SingletonTokenFactory, Variant> Drop for SingletonTokenGuard<Tag, Variant> {
    #[inline]
    fn drop(&mut self) {
        // Safety: This call is accompanied with the destruction of `self.token`.
        unsafe { Tag::r#return() };
    }
}

impl<Tag: ?Sized + SingletonTokenFactory, Variant: SingletonTokenVariant> ops::Deref
    for SingletonTokenGuard<Tag, Variant>
{
    type Target = SingletonToken<Tag, Variant>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.token
    }
}

impl<Tag: ?Sized + SingletonTokenFactory, Variant: SingletonTokenVariant> ops::DerefMut
    for SingletonTokenGuard<Tag, Variant>
{
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.token
    }
}

/// Error type returned when [`SingletonToken::new`] was called, but a token
/// has already been issued, and a new one cannot be issued until the old one
/// is returned to the factory by dropping [`SingletonTokenGuard`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SingletonTokenExhaustedError;

#[cfg(feature = "std")]
impl std::error::Error for SingletonTokenExhaustedError {
    fn description(&self) -> &str {
        "token already issued"
    }
}

impl fmt::Display for SingletonTokenExhaustedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "token already issued")
    }
}

impl<Tag: ?Sized + SingletonTokenFactory, Variant: SingletonTokenVariant>
    SingletonToken<Tag, Variant>
{
    /// Construct `Self`, using `Tag`'s [`SingletonTokenFactory`] implementation
    /// to ensure only one token is present at once.
    ///
    /// Returns an RAII guard that derefs to `SingletonToken` and returns the
    /// token when dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tokenlock::*;
    /// struct MyTag;
    /// impl_singleton_token_factory!(MyTag);
    ///
    /// type MyTokenLock<T> = TokenLock<T, SingletonTokenId<MyTag>>;
    /// type MyToken = SingletonToken<MyTag>;
    /// type MyTokenId = SingletonTokenId<MyTag>;
    ///
    /// static LOCK1: MyTokenLock<u32> = MyTokenLock::new(MyTokenId::new(), 1);
    /// static LOCK2: MyTokenLock<u32> = MyTokenLock::new(MyTokenId::new(), 1);
    ///
    /// // Create a singleton token with a runtime uniqueness check
    /// let mut token = MyToken::new().unwrap();
    ///
    /// LOCK1.read(&*token);
    /// LOCK2.write(&mut *token);
    /// ```
    ///
    /// The `SingletonTokenFactory` implementation remembers that a token
    /// has been issued, so attempts to issue two tokens of the same tag will
    /// fail:
    ///
    /// ```
    /// # use tokenlock::*;
    /// # struct MyTag;
    /// # impl_singleton_token_factory!(MyTag);
    /// let token = SingletonToken::<MyTag>::new().unwrap();
    /// assert!(SingletonToken::<MyTag>::new().is_err());
    /// ```
    #[inline]
    pub fn new() -> Result<SingletonTokenGuard<Tag, Variant>, SingletonTokenExhaustedError> {
        if Tag::take() {
            Ok(SingletonTokenGuard {
                // Safety: We established by calling `Tag::take` that the token
                //         doesn't exist yet
                token: unsafe { SingletonToken::new_unchecked() },
            })
        } else {
            Err(SingletonTokenExhaustedError)
        }
    }
}

impl<Tag: ?Sized + SingletonTokenFactory> SingletonTokenGuard<Tag> {
    /// Convert `SingletonTokenGuard` to the `!Sync` variant.
    #[inline]
    pub fn into_unsync(self) -> UnsyncSingletonTokenGuard<Tag> {
        // Suppress `self`'s destructor
        mem::forget(self);

        SingletonTokenGuard {
            // Safety: The previous token has just been removed
            token: unsafe { SingletonToken::new_unchecked() },
        }
    }
}

impl<Tag: ?Sized + SingletonTokenFactory> UnsyncSingletonTokenGuard<Tag> {
    /// Convert `UnsyncSingletonToken` to the `Sync` variant.
    #[inline]
    pub fn into_sync(self) -> SingletonTokenGuard<Tag> {
        // Suppress `self`'s destructor
        mem::forget(self);

        SingletonTokenGuard {
            // Safety: The previous token has just been removed
            token: unsafe { SingletonToken::new_unchecked() },
        }
    }
}
