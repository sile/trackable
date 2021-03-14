//! This crate provides functionalities to
//! define [trackable](trait.Trackable.html) objects and track those.
//!
//! Below is an example that tracks failure of an I/O operation:
//!
//! ```no_run
//! #[macro_use]
//! extern crate trackable;
//!
//! use trackable::error::Failure;
//!
//! fn foo() -> Result<(), Failure> {
//!     track!(std::fs::File::open("/path/to/non_existent_file").map_err(Failure::from_error))?;
//!     Ok(())
//! }
//! fn bar() -> Result<(), Failure> {
//!     track!(foo())?;
//!     Ok(())
//! }
//! fn baz() -> Result<(), Failure> {
//!     track!(bar())?;
//!     Ok(())
//! }
//!
//! fn main() {
//!     let result = baz();
//!     assert!(result.is_err());
//!
//!     let error = result.err().unwrap();
//!     assert_eq!(format!("\r{}", error).replace('\\', "/"), r#"
//! Failed (cause; No such file or directory)
//! HISTORY:
//!   [0] at src/lib.rs:7
//!   [1] at src/lib.rs:12
//!   [2] at src/lib.rs:16
//! "#);
//! }
//! ```
//!
//! This example used the built-in `Failure` type,
//! but you can easily define your own trackable error types.
//! See the documentaion of [error](error/index.html) module for more details.
#![warn(missing_docs)]

extern crate trackable1;
#[cfg_attr(test, macro_use)]
extern crate trackable_derive;

#[doc(hidden)]
pub use trackable_derive::*;

#[macro_use]
mod macros;

// for `trackable_derive`
mod trackable {
    pub use super::*;
}

pub mod error;
pub mod result;

pub use trackable1::Trackable;

pub use trackable1::History;

pub use trackable1::Location;

#[cfg(test)]
mod test {
    use super::*;
    use error::Failure;

    #[test]
    fn it_works() {
        fn foo() -> Result<(), Failure> {
            track!(std::fs::File::open("/path/to/non_existent_file")
                .map_err(|e| Failure::from_error(format!("{:?}", e.kind()))))?;
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

        let result = baz();
        assert!(result.is_err());

        let error = result.err().unwrap();
        assert_eq!(
            format!("\n{}", error).replace('\\', "/"),
            r#"
Failed (cause; NotFound)
HISTORY:
  [0] at src/lib.rs:77
  [1] at src/lib.rs:82
  [2] at src/lib.rs:86
"#
        );
    }
}
