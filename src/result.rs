//! Trackable [`Result`] types for main and test functions.
//!
//! [`Result`]: https://doc.rust-lang.org/std/result/enum.Result.html
use error::TopLevelError;

/// A variant of [`Result`] for top-level functions that return a trackable error on failure.
///
/// [`Result`]: https://doc.rust-lang.org/std/result/enum.Result.html
pub type TopLevelResult = Result<(), TopLevelError>;

/// A variant of [`Result`] for main functions that return a trackable error on failure.
///
/// [`Result`]: https://doc.rust-lang.org/std/result/enum.Result.html
pub type MainResult = TopLevelResult;

/// A variant of [`Result`] for unit tests that return a trackable error on failure.
///
/// [`Result`]: https://doc.rust-lang.org/std/result/enum.Result.html
pub type TestResult = TopLevelResult;
