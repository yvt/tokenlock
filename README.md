# tokenlock

[<img src="https://docs.rs/tokenlock/badge.svg" alt="docs.rs">](https://docs.rs/tokenlock/)

This crate provides a cell type, `TokenLock`, whose contents can only be
accessed by an unforgeable token.

## Examples

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
# use tokenlock::*;
# use std::thread;
let mut token = ArcToken::new();
let token = token.borrow_as_unsync();
let (token_1, token_2) = (&token, &token);

thread::Builder::new().spawn(move || {
    let _ = token_2;
});

let _ = token_1;
```

License: MIT/Apache-2.0
