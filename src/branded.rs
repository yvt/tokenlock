//! Lifetime-branded tokens (a.k.a. GhostCell)
use crate::{
    singleton::{
        SingletonToken, SingletonTokenId, SingletonTokenRef, SingletonTokenRefMut,
        UnsyncSingletonToken, UnsyncSingletonTokenRef, UnsyncSingletonTokenRefMut,
    },
    TokenLock, UnsyncTokenLock,
};

/// Lifetime-branded tag for use with [`SingletonToken`].
///
/// This type is invariant over `'brand`, although this could be just covariant
/// without loss of soundness.
pub struct BrandedTag<'brand> {
    _invariant: fn(&'brand ()) -> &'brand (),
}

/// Lifetime-branded token that can be used to access the contents of a
/// `TokenLock<T, `[`BrandedTokenId`]`<'brand>>`.
/// Created by [`with_branded_token`].
pub type BrandedToken<'brand> = SingletonToken<BrandedTag<'brand>>;

/// Zero-sized logical equivalent of `&'a `[`BrandedToken`]`<'brand>`.
pub type BrandedTokenRef<'a, 'brand> = SingletonTokenRef<'a, BrandedTag<'brand>>;

/// Zero-sized logical equivalent of `&'a mut `[`BrandedToken`]`<'brand>`.
pub type BrandedTokenRefMut<'a, 'brand> = SingletonTokenRefMut<'a, BrandedTag<'brand>>;

/// The `!Sync` variant of [`BrandedToken`].
pub type UnsyncBrandedToken<'brand> = UnsyncSingletonToken<BrandedTag<'brand>>;

/// Zero-sized logical equivalent of `&'a `[`UnsyncBrandedToken`]`<'brand>`.
/// The `!Sync` variant of [`BrandedTokenRef`].
pub type UnsyncBrandedTokenRef<'a, 'brand> = UnsyncSingletonTokenRef<'a, BrandedTag<'brand>>;

/// Zero-sized logical equivalent of `&'a mut `[`UnsyncBrandedToken`]`<'brand>`.
/// The `!Sync` variant of [`BrandedTokenRefMut`].
pub type UnsyncBrandedTokenRefMut<'a, 'brand> = UnsyncSingletonTokenRefMut<'a, BrandedTag<'brand>>;

/// Lifetime-branded token that cannot be used to access the contents of a
/// `TokenLock<T, `[`BrandedTokenId`]`<'brand>>` but can be used to create one.
/// Can be `default`-constructed.
pub type BrandedTokenId<'brand> = SingletonTokenId<BrandedTag<'brand>>;

/// A mutual exclusive primitive that can be accessed by presenting a
/// [`BrandedToken`] with the correct brand lifetime parameter.
pub type BrandedTokenLock<'brand, T> = TokenLock<T, BrandedTokenId<'brand>>;

/// Like [`BrandedTokenLock`] but requires presenting [`UnsyncBrandedToken`],
/// which is [`Unsync`]. This subtle difference allows it to be `Sync` even if
/// `T` is not.
///
/// [`Unsync`]: crate::Unsync
pub type UnsyncBrandedTokenLock<'brand, T> = UnsyncTokenLock<T, BrandedTokenId<'brand>>;

/// Call the provieded closure with a brand new [`BrandedToken`], which can
/// only be used throughout the duration of the function call.
///
/// This pattern is known as [GhostCell][1] and has been formally proven for
/// soundness (excluding the extensions provided by this crate).
///
/// [1]: http://plv.mpi-sws.org/rustbelt/ghostcell/
#[inline]
pub fn with_branded_token<R>(f: impl for<'brand> FnOnce(BrandedToken<'brand>) -> R) -> R {
    // Safety: As `f` is generic over `'brand`, and `BrandedToken::
    // new_unchecked` is `unsafe fn`, `f` cannot fabricate another instance of
    // `BrandedToken<'brand>` nor keep the given `BrandedToken` for later use.
    let token = unsafe { BrandedToken::new_unchecked() };
    f(token)
}
