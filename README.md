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

License: MIT/Apache-2.0
