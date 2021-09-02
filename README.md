# tokenlock

[<img src="https://docs.rs/tokenlock/badge.svg" alt="docs.rs">](https://docs.rs/tokenlock/)

This crate provides a cell type, `TokenLock`, which can only be borrowed
by presenting the correct unforgeable token, thus decoupling permissions
from data.

## Examples

### Basics

```rust
let mut token = ArcToken::new();

let lock = TokenLock::new(token.id(), 1);
assert_eq!(*lock.read(&token), 1);

let mut guard = lock.write(&mut token);
assert_eq!(*guard, 1);
*guard = 2;
```

Only the original `Token`'s owner can access its contents. `Token`
cannot be cloned:

```rust
let lock = Arc::new(TokenLock::new(token.id(), 1));

let lock_1 = Arc::clone(&lock);
thread::Builder::new().spawn(move || {
    let lock_1 = lock_1;
    let mut token_1 = token;

    // I have `Token` so I can get a mutable reference to the contents
    lock_1.write(&mut token_1);
}).unwrap();

// can't access the contents; I no longer have `Token`
// lock.write(&mut token);
```

### Lifetimes

The lifetime of the returned reference is limited by both of the `TokenLock`
and `Token`.

```rust
let mut token = ArcToken::new();
let lock = TokenLock::new(token.id(), 1);
let guard = lock.write(&mut token);
drop(lock); // compile error: `guard` cannot outlive `TokenLock`
drop(guard);
```

```rust
drop(token); // compile error: `guard` cannot outlive `Token`
drop(guard);
```

It also prevents from forming a reference to the contained value when
there already is a mutable reference to it:

```rust
let write_guard = lock.write(&mut token);
let read_guard = lock.read(&token); // compile error
drop(write_guard);
```

While allowing multiple immutable references:

```rust
let read_guard1 = lock.read(&token);
let read_guard2 = lock.read(&token);
```

### Use case: Linked lists

An operating system kernel often needs to store the global state in a global
variable. Linked lists are a common data structure used in a kernel, but
Rust's ownership does not allow forming `'static` references into values
protected by a mutex. Common work-arounds, such as smart pointers and index
references, take a heavy toll on a small microcontroller with a single-issue
in-order pipeline and no hardware multiplier.

```rust
struct Process {
    prev: Option<& /* what lifetime? */ Process>,
    next: Option<& /* what lifetime? */ Process>,
    state: u8,
    /* ... */
}
struct SystemState {
    first_process: Option<& /* what lifetime? */ Process>,
    process_pool: [Process; 64],
}
static STATE: Mutex<SystemState> = todo!();
```

`tokenlock` makes the `'static` reference approach possible by detaching the
lock granularity from the protected data's granularity.

```rust
use tokenlock::*;
use std::cell::Cell;
struct Tag;
impl_singleton_token_factory!(Tag);

type KLock<T> = UnsyncTokenLock<T, SingletonTokenId<Tag>>;
type KLockToken = UnsyncSingletonToken<Tag>;
type KLockTokenId = SingletonTokenId<Tag>;

struct Process {
    prev: KLock<Option<&'static Process>>,
    next: KLock<Option<&'static Process>>,
    state: KLock<u8>,
    /* ... */
}
struct SystemState {
    first_process: KLock<Option<&'static Process>>,
    process_pool: [Process; 1],
}
static STATE: SystemState = SystemState {
    first_process: KLock::new(KLockTokenId::new(), None),
    process_pool: [
        Process {
            prev: KLock::new(KLockTokenId::new(), None),
            next: KLock::new(KLockTokenId::new(), None),
            state: KLock::new(KLockTokenId::new(), 0),
        }
    ],
};
```

## Token types

This crate provides the following types implementing `Token`.

(**`std` only**) `RcToken` and `ArcToken` ensure their uniqueness by
reference-counted memory allocations.

`SingletonToken<Tag>` is a singleton token, meaning only one of such
instance can exist at any point of time during the program's execution.
`impl_singleton_token_factory!` instantiates a `static` flag to indicate
`SingletonToken`'s liveness and allows you to construct it safely by
`SingletonToken::new`. Alternatively, you can use
`SingletonToken::new_unchecked`, but this is unsafe if misused.

`BrandedToken<'brand>` implements an extension of [`GhostCell`][1]. It's
created by `with_branded_token` or `with_branded_token_async`, which
makes the created token available only within the provided closure or the
created `Future`. This token incurs no runtime cost.

[1]: http://plv.mpi-sws.org/rustbelt/ghostcell/

## `!Sync` tokens

`UnsyncTokenLock` is similar to `TokenLock` but designed for non-`Sync`
tokens and has relaxed requirements on the inner type for thread safety.
Specifically, it can be `Sync` even if the inner type is not `Sync`. This
allows for storing non-`Sync` cells such as `Cell` and reading and
writing them using shared references (all of which must be on the same
thread because the token is `!Sync`) to the token.

```rust
use std::cell::Cell;
let mut token = ArcToken::new();
let lock = Arc::new(UnsyncTokenLock::new(token.id(), Cell::new(1)));

let lock_1 = Arc::clone(&lock);
thread::Builder::new().spawn(move || {
    // "Lock" the token to the current thread using
    // `ArcToken::borrow_as_unsync`
    let token = token.borrow_as_unsync();

    // Shared references can alias
    let (token_1, token_2) = (&token, &token);

    lock_1.read(token_1).set(2);
    lock_1.read(token_2).set(4);
}).unwrap();
```

`!Sync` tokens, of course, cannot be shared between threads:

```rust
let mut token = ArcToken::new();
let token = token.borrow_as_unsync();
let (token_1, token_2) = (&token, &token);

// compile error: `&ArcTokenUnsyncRef` is not `Send` because
//                `ArcTokenUnsyncRef` is not `Sync`
thread::Builder::new().spawn(move || {
    let _ = token_2;
});

let _ = token_1;
```

## Cargo Features

 - **`std`** enables the items that depend on `std`.
 - **`unstable`** enables experimental items that are not subject to the
   semver guarantees.

## Related Work

 - [`ghost-cell`][1] is the official implementation of [`GhostCell`][2] and
   has been formally proven to be sound. It provides an equivalent of
   `BrandedTokenLock` with a simpler, more focused interface.

 - `SCell` from [`singleton-cell`][3] is a more generalized version of
   `GhostCell` and accepts any singleton token types, and thus it's more
   closer to our `TokenLock`. It provides equivalents of our
   `BrandedToken` and `SingletonToken` out-of-box. It trades away
   non-ZST token types for a unique advantage: `SCell<Key, [T]>` can be
   transposed to `[SCell<Key, T>]`.

 - [`qcell`][4] provides multiple cell types with different check
   mechanisms. `QCell` uses a 32-bit integer as a token identifier, `TCell`
   and `TLCell` use a marker type, and `LCell` uses lifetime branding.

[1]: https://crates.io/crates/ghost-cell
[2]: http://plv.mpi-sws.org/rustbelt/ghostcell/
[3]: https://crates.io/crates/singleton-cell
[4]: https://crates.io/crates/qcell

License: MIT/Apache-2.0
