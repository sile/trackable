//! Functionalities for implementing trackable errors and operating on those.
//!
//! You can easily define your own trackable error types as follows:
//!
//! ```
//! #[macro_use]
//! extern crate trackable;
//! use trackable::error::{TrackableError, ErrorKind, ErrorKindExt};
//!
//! #[derive(Debug, TrackableError)]
//! #[trackable(error_kind = "MyErrorKind")]
//! struct MyError(TrackableError<MyErrorKind>);
//! impl From<std::io::Error> for MyError {
//!     fn from(f: std::io::Error) -> Self {
//!         // Any I/O errors are considered critical
//!         MyErrorKind::Critical.cause(f).into()
//!     }
//! }
//!
//! # #[allow(dead_code)]
//! #[derive(Debug, PartialEq, Eq)]
//! enum MyErrorKind {
//!     Critical,
//!     NonCritical,
//! }
//! impl ErrorKind for MyErrorKind {}
//!
//! fn main() {
//!     // Tracks an error
//!     let error: MyError = MyErrorKind::Critical.cause("something wrong").into();
//!     let error = track!(error);
//!     let error = track!(error, "I passed here");
//!     assert_eq!(format!("\nError: {}", error).replace('\\', "/"), r#"
//! Error: Critical (cause; something wrong)
//! HISTORY:
//!   [0] at src/error.rs:27
//!   [1] at src/error.rs:28 -- I passed here
//! "#);
//!
//!     // Tries to execute I/O operation
//!     let result = (|| -> Result<_, MyError> {
//!         let f = track!(std::fs::File::open("/path/to/non_existent_file")
//!                        .map_err(MyError::from))?;
//!         Ok(f)
//!     })();
//!     let error = result.err().unwrap();
//!     let cause = error.concrete_cause::<std::io::Error>().unwrap();
//!     assert_eq!(cause.kind(), std::io::ErrorKind::NotFound);
//! }
//! ```
//!
//! # `TrackableError` drive macro
//!
//! If it is specified (i.e., `#[derive(TrackableError)]`),
//! the following traits will be automatically implemented in the target error type:
//! - `Trackable`
//! - `Error`
//! - `Display`
//! - `Deref<Target = TrackableError<$error_kind>>`
//! - `From<$error_kind>`
//! - `From<TrackableError<$error_kind>>`
//! - `From<$target_error_type> for TrackableError<$error_kind>`
//!
//! The default value of `$error_kind` is `ErrorKind`.
//! It can be customized by using `#[trackable(error_type = "$error_kind")]` attribute.
//!
//! The target error type must be a newtype (i.e., a tuple struct that has a single element) of `TrackableError`.
use std::error::Error;

use super::Location;

/// Boxed `Error` object.
pub type BoxError = Box<dyn Error + Send + Sync>;

/// Boxed `ErrorKind` object.
pub type BoxErrorKind = Box<dyn ErrorKind + Send + Sync>;

/// `History` type specialized for `TrackableError`.
pub type History = ::History<Location>;

pub use trackable1::error::Failed;

pub use trackable1::error::Failure;

pub use trackable1::error::IoError;

/// An `Error` type for unit tests.
pub type TestError = TopLevelError;

/// An `Error` type for `main` function.
pub type MainError = TopLevelError;

pub use trackable1::error::TopLevelError;

pub use trackable1::error::ErrorKind;

pub use trackable1::error::ErrorKindExt;

pub use trackable1::error::TrackableError;

#[cfg(test)]
mod test {
    use super::*;
    use std;

    #[test]
    fn it_works() {
        #[derive(Debug, TrackableError)]
        #[trackable(error_kind = "MyErrorKind")]
        struct MyError(TrackableError<MyErrorKind>);
        impl From<std::io::Error> for MyError {
            fn from(f: std::io::Error) -> Self {
                // Any I/O errors are considered critical
                MyErrorKind::Critical.cause(f).into()
            }
        }

        #[allow(dead_code)]
        #[derive(Debug, PartialEq, Eq)]
        enum MyErrorKind {
            Critical,
            NonCritical,
        }
        impl ErrorKind for MyErrorKind {}

        // Tracks an error
        let error: MyError = MyErrorKind::Critical.cause("something wrong").into();
        let error = track!(error);
        let error = track!(error, "I passed here");
        assert_eq!(
            format!("\nError: {}", error).replace('\\', "/"),
            r#"
Error: Critical (cause; something wrong)
HISTORY:
  [0] at src/error.rs:128
  [1] at src/error.rs:129 -- I passed here
"#
        );

        // Tries to execute I/O operation
        let result = (|| -> Result<_, MyError> {
            let f =
                track!(std::fs::File::open("/path/to/non_existent_file").map_err(MyError::from,))?;
            Ok(f)
        })();
        let error = result.err().unwrap();
        let cause = error.concrete_cause::<std::io::Error>().unwrap();
        assert_eq!(cause.kind(), std::io::ErrorKind::NotFound);
    }
}
