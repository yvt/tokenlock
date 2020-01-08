use std::{hash, rc::Rc};

use super::Token;

/// An `Rc`-based unforgeable token used to access the contents of a
/// `TokenLock`.
///
/// This type is not `Clone` to ensure an exclusive access to [`TokenLock`].
///
/// [`TokenLock`]: crate::TokenLock
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct RcToken(UniqueId);

impl RcToken {
    pub fn new() -> Self {
        RcToken(UniqueId::new())
    }

    /// Construct an [`RcTokenId`] that equates to `self`.
    pub fn id(&self) -> RcTokenId {
        RcTokenId(self.0.clone())
    }
}

impl Default for RcToken {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl Token<RcTokenId> for RcToken {
    fn eq_id(&self, id: &RcTokenId) -> bool {
        self.0 == id.0
    }
}

/// Token that cannot be used to access the contents of a [`TokenLock`], but can
/// be used to create a new `TokenLock`.
///
/// [`TokenLock`]: crate::TokenLock
///
/// # Examples
///
/// `RcTokenId` can be cloned while [`RcToken`] cannot:
///
/// ```
/// # use tokenlock::*;
/// let token = RcToken::new();
/// let token_id = token.id();
/// let lock1 = TokenLock::new(token_id.clone(), 1);
/// let lock2 = TokenLock::new(token_id, 2);
/// ```
///
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct RcTokenId(UniqueId);

#[derive(Debug, Clone)]
struct UniqueId(Rc<()>);

impl PartialEq for UniqueId {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
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
        UniqueId(Rc::new(()))
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
