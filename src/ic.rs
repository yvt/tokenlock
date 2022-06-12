//! Integer counter (IC) based tokens
//!
//! This module provides a token type that is generated from a global 128-bit
//! counter with thread-local pools to optimize for throughput. The runtime
//! memory consumption is proportional to the maximum number of threads that
//! existed simultaneously because the memory allocated to hold a freelist is
//! never released.
use alloc::boxed::Box;
use spin::Mutex;
use std::{cell::Cell, fmt, marker::PhantomData, num::NonZeroU64};

use super::{PinTokenLock, Token, TokenLock, Unsync, UnsyncPinTokenLock, UnsyncTokenLock};

/// A mutual exclusive primitive that can be accessed by presenting the matching
/// [`IcToken`].
pub type IcTokenLock<T> = TokenLock<T, IcTokenId>;

/// A [pinned] mutual exclusive primitive that can be accessed by presenting the
/// matching [`IcToken`].
///
/// [pinned]: core::pin
pub type IcPinTokenLock<T> = PinTokenLock<T, IcTokenId>;

/// Like [`IcTokenLock`] but requires presenting [`IcTokenUnsyncRef`],
/// which is [`Unsync`]. This subtle difference allows it to be `Sync` even if
/// `T` is not.
///
/// [`Unsync`]: crate::Unsync
pub type UnsyncIcTokenLock<T> = UnsyncTokenLock<T, IcTokenId>;

/// Like [`IcPinTokenLock`] but requires presenting [`IcTokenUnsyncRef`],
/// which is [`Unsync`]. This subtle difference allows it to be `Sync` even if
/// `T` is not.
///
/// [`Unsync`]: crate::Unsync
pub type UnsyncIcPinTokenLock<T> = UnsyncPinTokenLock<T, IcTokenId>;

/// A counter-based unforgeable token used to access the contents of a
/// `TokenLock`.
///
/// This type lacks a `Clone` implementation to ensure exclusive access to
/// [`TokenLock`].
///
/// [`TokenLock`]: crate::TokenLock
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct IcToken(UniqueId);

impl IcToken {
    #[inline]
    pub fn new() -> Self {
        IcToken(UniqueId::new())
    }

    /// Construct an [`IcTokenId`] that equates to `self`.
    #[inline]
    pub fn id(&self) -> IcTokenId {
        IcTokenId(self.0)
    }

    /// Borrow `self` as a non-`Sync` reference.
    ///
    /// Non-`Sync` tokens such as those created by this method can be used with
    /// [`UnsyncTokenLock`].
    ///
    /// [`UnsyncTokenLock`]: crate::UnsyncTokenLock
    #[inline]
    pub fn borrow_as_unsync(&mut self) -> IcTokenUnsyncRef<'_> {
        IcTokenUnsyncRef(&mut self.0, PhantomData)
    }
}

impl Default for IcToken {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl Token<IcTokenId> for IcToken {
    #[inline]
    fn eq_id(&self, id: &IcTokenId) -> bool {
        self.0 == id.0
    }
}

/// Represents a borrow of [`IcToken`] constrained to a single thread.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct IcTokenUnsyncRef<'a>(&'a mut UniqueId, PhantomData<MakeUnsync>);

struct MakeUnsync(std::cell::Cell<()>);

impl IcTokenUnsyncRef<'_> {
    /// Construct an [`IcTokenId`] that equates to `self`.
    #[inline]
    pub fn id(&self) -> IcTokenId {
        IcTokenId(*self.0)
    }
}

unsafe impl Token<IcTokenId> for IcTokenUnsyncRef<'_> {
    #[inline]
    fn eq_id(&self, id: &IcTokenId) -> bool {
        *self.0 == id.0
    }
}

// Safety: `PhantomData<Cell<()>` makes it `!Sync`
unsafe impl Unsync for IcTokenUnsyncRef<'_> {}

/// Token that cannot be used to access the contents of a [`TokenLock`], but can
/// be used to create a new `TokenLock`.
///
/// [`TokenLock`]: crate::TokenLock
///
/// # Examples
///
/// `IcTokenId` can be cloned while [`IcToken`] cannot:
///
/// ```
/// # use tokenlock::*;
/// let token = IcToken::new();
/// let token_id = token.id();
/// let lock1 = TokenLock::new(token_id.clone(), 1);
/// let lock2 = TokenLock::new(token_id, 2);
/// ```
///
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IcTokenId(UniqueId);

use pool::UniqueId;

/// Unique ID generator
mod pool {
    use super::*;

    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    pub(super) struct UniqueId {
        lower: u64,
        upper: NonZeroU64,
    }

    impl fmt::Debug for UniqueId {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{:08x}-{:08x}", self.upper.get(), self.lower)
        }
    }

    /// Represents a range of free IDs, signifying the range
    /// `(upper, lower)..=(upper, u64::MAX)` is available for allocation.
    #[derive(Clone, Copy)]
    struct Freelist {
        lower: u64,
        upper: NonZeroU64,
    }

    struct Pool {
        /// The list of `Node` that contains a valid freelist.
        first_occupied: Option<NodeRef>,
        /// The list of `Node` that doesn't contain a valid freelist.
        first_vacant: Option<NodeRef>,
        /// The last `Freelist::upper` assigned to a new freelist.
        last_upper: u64,
    }

    struct Node {
        freelist: Freelist,
        next: Option<NodeRef>,
    }

    type NodeRef = &'static mut Node;

    fn push(list: &mut Option<NodeRef>, node: NodeRef) {
        node.next = list.take();
        *list = Some(node);
    }

    fn pop(list: &mut Option<NodeRef>) -> Option<NodeRef> {
        let node = list.take()?;
        *list = node.next.take();
        Some(node)
    }

    static POOL: Mutex<Pool> = Mutex::new(Pool {
        first_occupied: None,
        first_vacant: None,
        last_upper: 0,
    });

    impl Pool {
        fn new_freelist(&mut self) -> Freelist {
            // Assign a new `upper` value. If `last_upper + 1 == 0`, that means
            // we ran out of unique `upper` values.
            let upper = self.last_upper.wrapping_add(1);
            let upper = NonZeroU64::new(upper).expect("out of upper half counter values");
            self.last_upper = upper.get();
            Freelist { lower: 0, upper }
        }
    }

    struct FreelistLease {
        freelist: Cell<Freelist>,
    }

    impl FreelistLease {
        #[cold]
        fn new() -> Self {
            let mut pool = POOL.lock();

            let freelist;
            if let Some(node) = pop(&mut pool.first_occupied) {
                // Reuse a previously used (and now returned) `Freelist`.
                freelist = node.freelist;
                push(&mut pool.first_vacant, node);
            } else {
                // Create a new `Freelist`.
                freelist = pool.new_freelist();
            }

            Self {
                freelist: Cell::new(freelist),
            }
        }

        /// Discard the current list, acquire a new one from the pool
        #[cold]
        fn renew(&self) {
            let new_lease = Self::new();
            self.freelist.set(new_lease.freelist.get());
            std::mem::forget(new_lease);
        }

        /// Get a `UniqueId`.
        #[inline]
        fn get(&self) -> UniqueId {
            let Freelist { lower, upper } = self.freelist.get();

            if let Some(next_lower) = lower.checked_add(1) {
                self.freelist.set(Freelist {
                    lower: next_lower,
                    upper,
                })
            } else {
                // This freelist is empty, get a new one
                self.renew();
            }

            UniqueId { lower, upper }
        }
    }

    impl Drop for FreelistLease {
        fn drop(&mut self) {
            let freelist = self.freelist.get();

            // Return the `Freelist` to the pool
            let mut pool = POOL.lock();
            let node = if let Some(node) = pop(&mut pool.first_vacant) {
                node.freelist = freelist;
                node
            } else {
                Box::leak(Box::new(Node {
                    freelist,
                    next: None,
                }))
            };
            push(&mut pool.first_occupied, node);
        }
    }

    std::thread_local! {
        static LOCAL_LEASE: FreelistLease = FreelistLease::new();
    }

    impl UniqueId {
        pub fn new() -> Self {
            // Take one from the local freelist
            LOCAL_LEASE.with(|lease| lease.get())
        }
    }
} // mod pool

#[test]
fn unique_id_hash() {
    let id1 = UniqueId::new();
    let id2 = id1.clone();
    let mut hm = std::collections::HashSet::new();
    assert!(hm.insert(id1));
    assert!(!hm.insert(id2)); // should have an identical hash
}

#[test]
fn uniqueness() {
    let _ = env_logger::builder().is_test(true).try_init();

    let (send, recv) = std::sync::mpsc::channel();
    let mut ids = std::collections::HashSet::new();

    for tid in 0..50 {
        let send = send.clone();
        std::thread::spawn(move || {
            log::debug!("Generator thread #{}: It is up", tid);
            for i in 1..=1000 {
                let id = IcToken::new();
                log::trace!(
                    "Generator thread #{}: Sending {:?} ({} of {})",
                    tid,
                    id.0,
                    i,
                    100
                );
                send.send(id).unwrap();
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
        });
    }
    drop(send);

    for id in recv {
        log::trace!("Main thread: Received {:?}", id.0);
        assert!(ids.insert(id.0), "{:?} was generated twice", id)
    }
}
