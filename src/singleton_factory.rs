use crate::std_core::{fmt, ops};

use crate::singleton::SingletonToken;

/// The RAII guard for a [`SingletonToken`] obtained through
/// [`SingletonToken::new`]. Returns the token to the factory automatically
/// when dropped.
pub struct SingletonTokenGuard<T: ?Sized + SingletonTokenFactory> {
    token: SingletonToken<T>,
}

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

/// Implement [`SingletonTokenFactory`] on a given type.
///
/// The generated implementation uses `AtomicBool` and therefore might not
/// compile on some targets.
#[macro_export]
macro_rules! impl_singleton_token_factory {
    ($ty:ty) => {
        const _: () = {
            use $crate::std_core::sync::atomic::{AtomicBool, Ordering};
            static TOKEN_ISSUED: AtomicBool = AtomicBool::new(false);

            unsafe impl $crate::SingletonTokenFactory for $ty {
                fn take() -> bool {
                    !TOKEN_ISSUED.swap(true, Ordering::Acquire)
                }
                unsafe fn r#return() {
                    TOKEN_ISSUED.store(false, Ordering::Release);
                }
            }
        };
    };
}

impl<T: ?Sized + SingletonTokenFactory> Drop for SingletonTokenGuard<T> {
    fn drop(&mut self) {
        // Safety: This call is accompanied with the destruction of `self.token`.
        unsafe { T::r#return() };
    }
}

impl<T: ?Sized + SingletonTokenFactory> ops::Deref for SingletonTokenGuard<T> {
    type Target = SingletonToken<T>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.token
    }
}

impl<T: ?Sized + SingletonTokenFactory> ops::DerefMut for SingletonTokenGuard<T> {
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

#[cfg(feature = "std")]
impl fmt::Display for SingletonTokenExhaustedError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "token already issued")
    }
}

impl<T: ?Sized + SingletonTokenFactory> SingletonToken<T> {
    /// Construct `Self`, using `T`'s [`SingletonTokenFactory`] implementation
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
    /// let mut token = SingletonToken::<MyTag>::new().unwrap();
    /// let lock1 = TokenLock::new(token.id(), 1);
    /// let lock2 = TokenLock::new(token.id(), 1);
    ///
    /// lock1.read(&*token);
    /// lock2.write(&mut *token);
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
    pub fn new() -> Result<SingletonTokenGuard<T>, SingletonTokenExhaustedError> {
        if T::take() {
            Ok(SingletonTokenGuard {
                // Safety: We established by calling `T::take` that the token
                //         doesn't exist yet
                token: unsafe { SingletonToken::new_unchecked() },
            })
        } else {
            Err(SingletonTokenExhaustedError)
        }
    }
}
