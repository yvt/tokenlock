# tokenlock

[<img src="https://docs.rs/tokenlock/badge.svg" alt="docs.rs">](https://docs.rs/tokenlock/)

Provides a `Send`-able cell type whose contents can be accessed only via an
inforgeable token.

## Examples

```rust
let mut token = Token::new();

let lock = TokenLock::new(&token, 1);
assert_eq!(*lock.read(&token).unwrap(), 1);

let mut guard = lock.write(&mut token).unwrap();
assert_eq!(*guard, 1);
*guard = 2;
```

`TokenLock` implements `Send` and `Sync` so it can be shared between threads,
but only the thread holding the original `Token` can access its contents.
`Token` cannot be cloned:

```rust
let lock = Arc::new(TokenLock::new(&token, 1));

let lock_1 = Arc::clone(&lock);
thread::Builder::new().spawn(move || {
    let lock_1 = lock_1;
    let mut token_1 = token;

    // I have `Token` so I can get a mutable reference to the contents
    lock_1.write(&mut token_1).unwrap();
}).unwrap();

// can't access the contents; I no longer have `Token`
// lock.write(&mut token).unwrap();
```

The lifetime of the returned reference is limited by both of the `TokenLock`
and `Token`.

```rust
let mut token = Token::new();
let lock = TokenLock::new(&token, 1);
let guard = lock.write(&mut token).unwrap();
drop(lock); // compile error: `guard` cannot outlive `TokenLock`
```

```rust
drop(token); // compile error: `guard` cannot outlive `Token`
```

It also prevents from forming a reference to the contained value when
there already is a mutable reference to it:

```rust
let write_guard = lock.write(&mut token).unwrap();
let read_guard = lock.read(&token).unwrap(); // compile error
```

While allowing multiple immutable references:

```rust
let read_guard1 = lock.read(&token).unwrap();
let read_guard2 = lock.read(&token).unwrap();
```

License: MIT/Apache-2.0
