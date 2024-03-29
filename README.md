# tokenlock

[<img src="https://docs.rs/tokenlock/badge.svg" alt="docs.rs">](https://docs.rs/tokenlock/)

This crate provides a cell type, `TokenLock`, which can only be borrowed
by presenting the correct unforgeable token, thus decoupling permissions
from data.

## Examples

### Basics

```rust
// Create a token
let mut token = IcToken::new();

// Create a keyhole by `token.id()` and use this to create a `TokenLock`.
let lock: IcTokenLock<i32> = TokenLock::new(token.id(), 1);
assert_eq!(*lock.read(&token), 1);

// Unlock the `TokenLock` using the matching token
let mut guard = lock.write(&mut token);
assert_eq!(*guard, 1);
*guard = 2;
```

Only the matching `Token`'s owner can access its contents. `Token`
cannot be cloned:

```rust
let lock = Arc::new(TokenLock::new(token.id(), 1));

let lock_1 = Arc::clone(&lock);
std::thread::spawn(move || {
    let lock_1 = lock_1;
    let mut token_1 = token;

    // I have `Token` so I can get a mutable reference to the contents
    lock_1.write(&mut token_1);
});

// can't access the contents; I no longer have `Token`
// lock.write(&mut token);
```

### Zero-sized tokens

Some token types, such as `BrandedToken` and `SingletonToken`, rely
solely on type safety and compile-time checks to guarantee uniqueness and
don't use runtime data for identification. As such, the keyholes for such
tokens can be default-constructed. `TokenLock::wrap` lets you construct a
`TokenLock` with a default-constructed keyhole.
On the other hand, creating such tokens usually has specific requirements.
See the following example that uses `with_branded_token`:

```rust
with_branded_token(|mut token| {
    // The lifetime of `token: BrandedToken<'brand>` is bound to
    // this closure.

    // lock: BrandedTokenLock<'brand, i32>
    let lock = BrandedTokenLock::wrap(42);

    lock.set(&mut token, 56);
    assert_eq!(lock.get(&token), 56);
});
```

### Lifetimes

The lifetime of the returned reference is limited by both of the `TokenLock`
and `Token`.

```rust
let mut token = IcToken::new();
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

type KLock<T> = UnsyncSingletonTokenLock<T, Tag>;
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

## Cell types

The `TokenLock` type family is comprised of the following types:

|            | `Sync` tokens    | `!Sync` tokens²        |
| ---------- | ---------------- | ---------------------- |
| Unpinned   | `TokenLock`      | `UnsyncTokenLock`      |
| Pinned¹    | `PinTokenLock`   | `UnsyncPinTokenLock`   |

<sub>¹That is, these types respect `T` being `!Unpin` and prevent the
exposure of `&mut T` through `&Self` or `Pin<&mut Self>`.</sub>

<sub>²`Unsync*TokenLock` require that tokens are `!Sync` (not sharable
across threads). In exchange, such cells can be `Sync` even if the contained
data is not `Sync`, just like `std::sync::Mutex`.</sub>

## Token types

This crate provides the following types implementing `Token`.

(**`std` only**) `IcToken` uses a global counter (with thread-local pools)
to generate unique 128-bit tokens.

(**`alloc` only**) `RcToken` and `ArcToken` ensure their uniqueness by
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

| Token ID (keyhole)             | Token (key)                       |
| ------------------------------ | --------------------------------- |
| `IcTokenId`                    | `IcToken` + `u128` comparison     |
| `RcTokenId`                    | `RcToken` + `usize` comparison    |
| `ArcTokenId`                   | `ArcToken` + `usize` comparison   |
| `SingletonTokenId<Tag>`        | `SingletonToken<Tag>`             |
| `BrandedTokenId<'brand>`       | `BrandedToken<'brand>`            |

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
std::thread::spawn(move || {
    // "Lock" the token to the current thread using
    // `ArcToken::borrow_as_unsync`
    let token = token.borrow_as_unsync();

    // Shared references can alias
    let (token_1, token_2) = (&token, &token);

    lock_1.read(token_1).set(2);
    lock_1.read(token_2).set(4);
});
```

`!Sync` tokens, of course, cannot be shared between threads:

```rust
let mut token = ArcToken::new();
let token = token.borrow_as_unsync();
let (token_1, token_2) = (&token, &token);

// compile error: `&ArcTokenUnsyncRef` is not `Send` because
//                `ArcTokenUnsyncRef` is not `Sync`
std::thread::spawn(move || {
    let _ = token_2;
});

let _ = token_1;
```

## Cargo Features

 - **`std`** enables the items that depend on `std` or `alloc`.
 - **`alloc`** enables the items that depend on `alloc`.
 - **`unstable`** enables experimental items that are not subject to the
   semver guarantees.
 - **`const-default_1`** enables the implementation of `ConstDefault` from
   [`const-default ^1`][].

[`const-default ^1`]: https://crates.io/crates/const-default/1.0.0

## Related Work

 - [`ghost-cell`][1] is the official implementation of [`GhostCell`][2] and
   has been formally proven to be sound. It provides an equivalent of
   `BrandedTokenLock` with a simpler, more focused interface.

 - `SCell` from [`singleton-cell`][3] is a more generalized version of
   `GhostCell` and accepts any singleton token types, and thus it's more
   closer to our `TokenLock`. It provides equivalents of our
   `BrandedToken` and `SingletonToken` out-of-box. It trades away
   non-ZST token types for an advantage: `SCell<Key, [T]>` can be transposed
   to `[SCell<Key, T>]`. It uses the [`singleton-trait`][5] crate (which did
   not exist when `tokenlock::SingletonToken` was added) to mark singleton
   token types.

 - [`qcell`][4] provides multiple cell types with different check
   mechanisms. `QCell` uses a 32-bit integer as a token identifier, `TCell`
   and `TLCell` use a marker type, and `LCell` uses lifetime branding.

 - `TokenCell` from [`token-cell`][6] is related to our `SingletonToken`,
   but like `SCell` (but differing slightly), it supports transposition
   from `&TokenCell<Token, &[T]>` to `&[TokenCell<Token, T>]`. It uses a
   custom trait to mark singleton token types.

[1]: https://crates.io/crates/ghost-cell
[2]: http://plv.mpi-sws.org/rustbelt/ghostcell/
[3]: https://crates.io/crates/singleton-cell
[4]: https://crates.io/crates/qcell
[5]: https://crates.io/crates/singleton-trait
[6]: https://crates.io/crates/token-cell

License: MIT/Apache-2.0
