# tokenlock

[<img src="https://docs.rs/tokenlock/badge.svg" alt="docs.rs">](https://docs.rs/tokenlock/)

Cell type whose contents can be accessed only via an inforgeable token.

## Examples

```rust
let mut token = Token::new();

let lock = TokenLock::new(&token, 1);
assert_eq!(*lock.read(&token).unwrap(), 1);

let mut guard = lock.write(&mut token).unwrap();
assert_eq!(*guard, 1);
*guard = 2;
```

The lifetime of the returned reference is limited by both of the `TokenLock`
and `Token`.

```rust
drop(lock); // compile error: cannot outlive `TokenLock`
```

```rust
drop(token); // compile error: cannot outlive `Token`
```

This also prevents from forming a reference to the contained value when
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
