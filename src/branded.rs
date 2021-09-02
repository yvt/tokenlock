//! Lifetime-branded tokens (a.k.a. GhostCell)
use crate::{
    singleton::{
        SingletonToken, SingletonTokenId, SingletonTokenRef, SingletonTokenRefMut,
        UnsyncSingletonToken, UnsyncSingletonTokenRef, UnsyncSingletonTokenRefMut,
    },
    PinTokenLock, TokenLock, UnsyncPinTokenLock, UnsyncTokenLock,
};

#[cfg(feature = "unstable")]
pub use crate::branded_async::*;

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
///
/// See [`with_branded_token`] for an example.
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

/// A pinned mutual exclusive primitive that can be accessed by presenting a
/// [`BrandedToken`] with the correct brand lifetime parameter.
pub type BrandedPinTokenLock<'brand, T> = PinTokenLock<T, BrandedTokenId<'brand>>;

/// Like [`BrandedTokenLock`] but requires presenting [`UnsyncBrandedToken`],
/// which is [`Unsync`]. This subtle difference allows it to be `Sync` even if
/// `T` is not.
///
/// [`Unsync`]: crate::Unsync
pub type UnsyncBrandedTokenLock<'brand, T> = UnsyncTokenLock<T, BrandedTokenId<'brand>>;

/// Like [`BrandedPinTokenLock`] but requires presenting [`UnsyncBrandedToken`],
/// which is [`Unsync`]. This subtle difference allows it to be `Sync` even if
/// `T` is not.
///
/// [`Unsync`]: crate::Unsync
pub type UnsyncBrandedPinTokenLock<'brand, T> = UnsyncPinTokenLock<T, BrandedTokenId<'brand>>;

/// Call the provided closure with a brand new [`BrandedToken`], which can
/// only be used throughout the duration of the function call.
///
/// This pattern is known as [GhostCell][1] and has been formally proven for
/// soundness (excluding the extensions provided by this crate).
///
/// [1]: http://plv.mpi-sws.org/rustbelt/ghostcell/
///
/// # Example
///
/// ```rust,edition2018
/// use rayon::prelude::*;
/// use tokenlock::{with_branded_token, BrandedTokenLock};
///
/// struct Node<'arena, 'brand> {
///     next: BrandedTokenLock<'brand, Option<&'arena Node<'arena, 'brand>>>,
/// }
///
/// with_branded_token(|mut token| {
///     let arena = [
///         Node { next: BrandedTokenLock::wrap(None) },
///         Node { next: BrandedTokenLock::wrap(None) },
///     ];
///
///     // Link the nodes together
///     arena[0].next.replace(&mut token, Some(&arena[1]));
///     arena[1].next.replace(&mut token, Some(&arena[0]));
///
///     // Unlike `Cell`, this doesn't prevent shared read-only access
///     arena.par_iter().for_each(|item| {
///         println!("{:p} is linked to {:p}", item, item.next.get(&token).unwrap());
///     });
/// });
/// ```
///
/// ```rust,edition2018
/// use rayon::prelude::*;
/// use std::sync::mpsc;
/// use tokenlock::{with_branded_token, UnsyncBrandedTokenLock};
///
/// with_branded_token(|mut token| {
///     let unsync_token = token.borrow_unsync_mut();
///
///     let senders: Vec<_> = (0..4)
///         .map(|_| UnsyncBrandedTokenLock::wrap(mpsc::channel().0))
///         .collect();
///
///     // `unsync_token` unlocks `UnsyncBrandedTokenLock`
///     let _ = senders[0].read(&*unsync_token).send(());
///
///     // `Sender` is `!Sync`, but that doesn't make `senders` `!Sync` because
///     // `UnsyncBrandedTokenLock` can only be borrowed by one thread at the
///     // same time
///     senders.par_iter().for_each(|item| println!("{:p}", item));
/// });
/// ```
#[inline]
pub fn with_branded_token<R>(f: impl for<'brand> FnOnce(BrandedToken<'brand>) -> R) -> R {
    // Safety: As `f` is generic over `'brand`, and `BrandedToken::
    // new_unchecked` is `unsafe fn`, `f` cannot fabricate another instance of
    // `BrandedToken<'brand>` nor keep the given `BrandedToken` for later use.
    let token = unsafe { BrandedToken::new_unchecked() };
    f(token)
}
