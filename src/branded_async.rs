use crate::BrandedToken;
use core::future::Future;

/// `FnOnce(BrandedToken<'brand>) -> impl Future`, used as a parameter type of
/// [`with_branded_token_async`]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "unstable")))]
pub trait IntoBrandedFuture<'brand> {
    /// The created `Future`'s type.
    type Future: Future<Output = Self::Output>;

    /// [`Self::Future`]'s output type.
    type Output;

    /// Consume `self` and the provided `BrandedToken` to produce a `Future`.
    fn into_branded_future(self, token: BrandedToken<'brand>) -> Self::Future;
}

impl<'brand, T, F> IntoBrandedFuture<'brand> for T
where
    T: FnOnce(BrandedToken<'brand>) -> F,
    F: Future,
{
    type Future = F;
    type Output = F::Output;

    #[inline]
    fn into_branded_future(self, token: BrandedToken<'brand>) -> Self::Future {
        (self)(token)
    }
}

impl<'brand, T, F, Ctx> IntoBrandedFuture<'brand> for (Ctx, T)
where
    T: FnOnce(Ctx, BrandedToken<'brand>) -> F,
    F: Future,
{
    type Future = F;
    type Output = F::Output;

    #[inline]
    fn into_branded_future(self, token: BrandedToken<'brand>) -> Self::Future {
        (self.1)(self.0, token)
    }
}

/// Call the provided closure with a brand new [`BrandedToken`], which can
/// only be used during the execution of the returned `Future`.
///
/// This pattern is an asynchronous extension of [GhostCell][1]. See
/// [`with_branded_token`][2] for the synchronous version.
///
/// [1]: http://plv.mpi-sws.org/rustbelt/ghostcell/
/// [2]: crate::with_branded_token
///
/// # Example
///
/// Passing `impl FnOnce(BrandedToken<'_>) -> impl Future` (a free `async fn`):
///
/// ```rust
/// use async_scoped::TokioScope;
/// use futures::executor::block_on;
/// use rayon::prelude::*;
/// use std::pin::Pin;
/// use tokenlock::{with_branded_token_async, BrandedTokenLock, BrandedToken};
/// # #[tokio::main]
/// # async fn main() {
///
/// struct Node<'arena, 'brand> {
///     next: BrandedTokenLock<'brand, Option<&'arena Node<'arena, 'brand>>>,
/// }
///
/// with_branded_token_async(task).await;
///
/// async fn task(mut token: BrandedToken<'_>) {
///     let mut token = token;
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
///     TokioScope::scope_and_block(|s| {
///         for node in arena.iter() {
///             let token = token.borrow();
///             s.spawn(async move {
///                 println!("{:p} is linked to {:p}", node, node.next.get(&*token).unwrap());
///             });
///         }
///     });
/// }
/// # }
/// ```
///
/// Passing `(T, impl FnOnce(T, BrandedToken<'_>) -> impl Future)`:
///
/// ```rust
/// # use futures::executor::block_on;
/// # use tokenlock::{with_branded_token_async, BrandedToken};
/// # #[tokio::main]
/// # async fn main() {
/// let mut value = 0;
/// with_branded_token_async((&mut value, task)).await;
/// assert_eq!(value, 42);
///
/// async fn task(borrowed_value: &mut i32, _token: BrandedToken<'_>) {
///     *borrowed_value = 42;
/// }
///
/// # }
/// ```
///
/// Closures don't work currently:
///
/// ```rust,compile_fail
/// # use futures::executor::block_on;
/// # use tokenlock::{with_branded_token_async, BrandedTokenLock, BrandedToken};
/// # #[tokio::main]
/// # async fn main() {
/// with_branded_token_async(|token: BrandedToken<'_>| async move {
///     let _ = token;
/// }).await;
/// # }
/// ```
#[inline]
#[cfg_attr(feature = "doc_cfg", doc(cfg(feature = "unstable")))]
pub fn with_branded_token_async<'a, F, R>(f: F) -> impl Future<Output = R> + 'a
where
    for<'brand> F: IntoBrandedFuture<'brand, Output = R> + 'a,
{
    async move {
        // Safety: As `f` is generic over `'brand`, and `BrandedToken::
        // new_unchecked` is `unsafe fn`, `f` cannot fabricate another instance of
        // `BrandedToken<'brand>` nor keep the given `BrandedToken` for later use.
        let token = unsafe { BrandedToken::new_unchecked() };
        f.into_branded_future(token).await
    }
}
