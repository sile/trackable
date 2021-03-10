trackable
=========

[![Crates.io: trackable](https://img.shields.io/crates/v/trackable.svg)](https://crates.io/crates/trackable)
[![Documentation](https://docs.rs/trackable/badge.svg)](https://docs.rs/trackable)
[![Actions Status](https://github.com/sile/trackable/workflows/CI/badge.svg)](https://github.com/sile/trackable/actions)
[![Coverage Status](https://coveralls.io/repos/github/sile/trackable/badge.svg?branch=master)](https://coveralls.io/github/sile/trackable?branch=master)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

`trackable` provides functionalities to define trackable objects and track those.

[Documentation](https://docs.rs/trackable)

Below code is an example that tracks failure of an I/O operation:

```rust
#[macro_use]
extern crate trackable;

use trackable::error::Failure;

fn foo() -> Result<(), Failure> {
    track!(std::fs::File::open("/path/to/non_existent_file").map_err(Failure::from_error))?;
    Ok(())
}
fn bar() -> Result<(), Failure> {
    track!(foo())?;
    Ok(())
}
fn baz() -> Result<(), Failure> {
    track!(bar())?;
    Ok(())
}

fn main() {
    let result = baz();
    assert!(result.is_err());

    let error = result.err().unwrap();
    assert_eq!(format!("\r{}", error), r#"
Failed (cause; No such file or directory)
HISTORY:
  [0] at rust_out:<anon>:7
  [1] at rust_out:<anon>:12
  [2] at rust_out:<anon>:16
"#);
}
```

This example used the built-in `Failure` type, but you can easily define your own trackable error types.
See the documentaion of [error](https://docs.rs/trackable/0.2/trackable/error/index.html) module for more details.
