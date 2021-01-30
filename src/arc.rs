use std::{hash, marker::PhantomData, sync::Arc};

use super::{Token, Unsync};

/// An `Arc`-based unforgeable token used to access the contents of a
/// `TokenLock`.
///
/// This type lacks a `Clone` implementation to ensure exclusive access to
/// [`TokenLock`].
///
/// [`TokenLock`]: crate::TokenLock
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ArcToken(UniqueId);

impl ArcToken {
    pub fn new() -> Self {
        ArcToken(UniqueId::new())
    }

    /// Construct an [`ArcTokenId`] that equates to `self`.
    pub fn id(&self) -> ArcTokenId {
        ArcTokenId(self.0.clone())
    }

    /// Borrow `self` as a non-`Sync` reference.
    ///
    /// Non-`Sync` tokens such as those created by this method can be used with
    /// [`UnsyncTokenLock`].
    ///
    /// [`UnsyncTokenLock`]: crate::UnsyncTokenLock
    pub fn borrow_as_unsync(&mut self) -> ArcTokenUnsyncRef<'_> {
        ArcTokenUnsyncRef(&mut self.0, PhantomData)
    }
}

impl Default for ArcToken {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl Token<ArcTokenId> for ArcToken {
    fn eq_id(&self, id: &ArcTokenId) -> bool {
        self.0 == id.0
    }
}

/// Represents a borrow of [`ArcToken`] constrained to a single thread.
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct ArcTokenUnsyncRef<'a>(&'a mut UniqueId, PhantomData<MakeUnsync>);

struct MakeUnsync(std::cell::Cell<()>);

impl ArcTokenUnsyncRef<'_> {
    /// Construct an [`ArcTokenId`] that equates to `self`.
    pub fn id(&self) -> ArcTokenId {
        ArcTokenId(self.0.clone())
    }
}

unsafe impl Token<ArcTokenId> for ArcTokenUnsyncRef<'_> {
    fn eq_id(&self, id: &ArcTokenId) -> bool {
        *self.0 == id.0
    }
}

// Safety: `PhantomData<Cell<()>` makes it `!Sync`
unsafe impl Unsync for ArcTokenUnsyncRef<'_> {}

/// Token that cannot be used to access the contents of a [`TokenLock`], but can
/// be used to create a new `TokenLock`.
///
/// [`TokenLock`]: crate::TokenLock
///
/// # Examples
///
/// `ArcTokenId` can be cloned while [`ArcToken`] cannot:
///
/// ```
/// # use tokenlock::*;
/// let token = ArcToken::new();
/// let token_id = token.id();
/// let lock1 = TokenLock::new(token_id.clone(), 1);
/// let lock2 = TokenLock::new(token_id, 2);
/// ```
///
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ArcTokenId(UniqueId);

#[derive(Debug, Clone)]
struct UniqueId(Arc<()>);

impl PartialEq for UniqueId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for UniqueId {}

impl hash::Hash for UniqueId {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        (&*self.0 as *const ()).hash(state)
    }
}

impl UniqueId {
    pub fn new() -> Self {
        UniqueId(Arc::new(()))
    }
}

#[test]
fn unique_id_hash() {
    let id1 = UniqueId::new();
    let id2 = id1.clone();
    let mut hm = std::collections::HashSet::new();
    assert!(hm.insert(id1));
    assert!(!hm.insert(id2)); // should have an identical hash
}
