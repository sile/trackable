//! Functionalities for implementing trackable errors and operating on those.
//!
//! You can easily define your own trackable error types as follows:
//!
//! ```
//! #[macro_use]
//! extern crate trackable;
//! use trackable::error::{TrackableError, IntoTrackableError, ErrorKind, ErrorKindExt};
//!
//! type MyError = TrackableError<MyErrorKind>;
//!
//! # #[allow(dead_code)]
//! #[derive(Debug, PartialEq, Eq)]
//! enum MyErrorKind {
//!     Critical,
//!     NonCritical,
//! }
//! impl ErrorKind for MyErrorKind {
//!     fn is_tracking_needed(&self) -> bool {
//!         *self == MyErrorKind::Critical  // Only critical errors are tracked
//!     }
//! }
//! impl IntoTrackableError<std::io::Error> for MyErrorKind {
//!     fn into_trackable_error(e: std::io::Error) -> MyError {
//!         // Any I/O errors are considered critical
//!         MyErrorKind::Critical.cause(e)
//!     }
//! }
//!
//! fn main() {
//!     // Tracks an error
//!     let error: MyError = MyErrorKind::Critical.cause("something wrong");
//!     let error = track!(error);
//!     let error = track!(error, "I passed here");
//!     assert_eq!(format!("\nError: {}", error), r#"
//! Error: Critical (cause; something wrong)
//! HISTORY:
//!   [0] at <anon>:28
//!   [1] at <anon>:29; I passed here
//! "#);
//!
//!     // Tries to execute I/O operation
//!     let result = (|| -> Result<_, MyError> {
//!         let f = track_try!(std::fs::File::open("/path/to/non_existent_file"));
//!         Ok(f)
//!     })();
//!     let error = result.err().unwrap();
//!     let cause = error.concrete_cause::<std::io::Error>().unwrap();
//!     assert_eq!(cause.kind(), std::io::ErrorKind::NotFound);
//! }
//! ```
use std::fmt;
use std::error::Error;
use std::sync::Arc;

use super::{TrackingNumber, Location, Trackable};

/// Boxed `Error` object.
pub type BoxError = Box<Error + Send + Sync>;

/// Boxed `ErrorKind` object.
pub type BoxErrorKind = Box<ErrorKind + Send + Sync>;

/// `History` type specialized for `TrackableError`.
pub type History = ::History<Event>;

/// Built-in `ErrorKind` implementation which represents opaque errors.
#[derive(Debug, Default, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Failed;
impl ErrorKind for Failed {
    fn description(&self) -> &str {
        "Failed"
    }
}
impl IntoTrackableError<BoxError> for Failed {
    fn into_trackable_error(cause: BoxError) -> Failure {
        Failed.cause(cause)
    }
}
impl IntoTrackableError<String> for Failed {
    fn into_trackable_error(cause: String) -> Failure {
        Failed.cause(cause)
    }
}
impl<'a> IntoTrackableError<&'a str> for Failed {
    fn into_trackable_error(cause: &'a str) -> Failure {
        Failed.cause(cause)
    }
}

/// `TrackableError` type specialized for `Failed`.
pub type Failure = TrackableError<Failed>;

/// This trait represents a error kind which `TrackableError` can have.
pub trait ErrorKind: fmt::Debug {
    /// A short description of the error kind.
    ///
    /// This is used for the description of the error that contains it.
    ///
    /// The default implementation always returns `"An error"`.
    fn description(&self) -> &str {
        "An error"
    }

    /// Displays this kind.
    ///
    /// The default implementation uses the debugging form of this.
    fn display(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }

    /// Returns whether the error of this kind is needed to be tracked.
    ///
    /// The default implementation always returns `true`.
    fn is_tracking_needed(&self) -> bool {
        true
    }
}
impl ErrorKind for String {
    fn description(&self) -> &str {
        self
    }
}

/// An extention of `ErrorKind` trait.
///
/// This provides convenient functions to create a `TrackableError` instance of this kind.
pub trait ErrorKindExt: ErrorKind + Sized {
    /// Makes a `TrackableError` instance without cause.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use trackable::error::{Failed, ErrorKindExt};
    ///
    /// let e = Failed.error();
    /// assert!(e.cause().is_none());
    /// ```
    fn error(self) -> TrackableError<Self> {
        self.into()
    }

    /// Makes a `TrackableError` instance with the specified `cause`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::error::Error;
    /// use trackable::error::{Failed, ErrorKindExt};
    ///
    /// let e = Failed.cause("something wrong");
    /// assert_eq!(e.cause().unwrap().to_string(), "something wrong");
    /// ```
    fn cause<E>(self, cause: E) -> TrackableError<Self>
        where E: Into<BoxError>
    {
        TrackableError::new(self, cause.into())
    }

    /// Takes over from other `TrackableError` instance.
    ///
    /// If either `from.in_tracking()` or `self.is_tracking_needed()` is `true`,
    /// tracking of the returning `TrackableError` will be enabled.
    ///
    /// The history of `from` will be preserved.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use]
    /// # extern crate trackable;
    /// #
    /// use trackable::error::{ErrorKind, ErrorKindExt};
    ///
    /// #[derive(Debug)]
    /// struct Kind0;
    /// impl ErrorKind for Kind0 {}
    ///
    /// #[derive(Debug)]
    /// struct Kind1;
    /// impl ErrorKind for Kind1 {}
    ///
    /// fn main() {
    ///   let e = Kind0.error();
    ///   let e = track!(e);
    ///
    ///   let e = Kind1.takes_over(e);
    ///   let e = track!(e);
    ///
    ///   assert_eq!(format!("\nERROR: {}", e), r#"
    /// ERROR: Kind1
    /// HISTORY:
    ///   [0] at <anon>:16
    ///   [1] takes over from `Kind0`
    ///   [2] at <anon>:19
    /// "#);
    /// }
    /// ```
    fn takes_over<K>(self, from: TrackableError<K>) -> TrackableError<Self>
        where K: ErrorKind + Send + Sync + 'static
    {
        let mut history = from.history;
        if let Some(ref mut h) = history {
            h.add(Event::TakeOver(Arc::new(Box::new(from.kind))));
        } else if self.is_tracking_needed() {
            history = Some(History::new());
        }
        TrackableError {
            kind: self,
            cause: from.cause,
            history: history,
            tracking_number: from.tracking_number,
        }
    }
}
impl<T: ErrorKind> ErrorKindExt for T {}

/// Trackable error.
///
/// # Examples
///
/// Defines your own `Error` type.
///
/// ```
/// #[macro_use]
/// extern crate trackable;
/// use trackable::error::{TrackableError, IntoTrackableError, ErrorKind, ErrorKindExt};
///
/// type MyError = TrackableError<MyErrorKind>;
///
/// # #[allow(dead_code)]
/// #[derive(Debug, PartialEq, Eq)]
/// enum MyErrorKind {
///     Critical,
///     NonCritical,
/// }
/// impl ErrorKind for MyErrorKind {
///     fn is_tracking_needed(&self) -> bool {
///         *self == MyErrorKind::Critical  // Only critical errors are tracked
///     }
/// }
/// impl IntoTrackableError<std::io::Error> for MyErrorKind {
///     fn into_trackable_error(e: std::io::Error) -> MyError {
///         // Any I/O errors are considered critical
///         MyErrorKind::Critical.cause(e)
///     }
/// }
///
/// fn main() {
///     // Tracks an error
///     let error: MyError = MyErrorKind::Critical.cause("something wrong");
///     let error = track!(error);
///     let error = track!(error, "I passed here");
///     assert_eq!(format!("\nError: {}", error), r#"
/// Error: Critical (cause; something wrong)
/// HISTORY:
///   [0] at <anon>:28
///   [1] at <anon>:29; I passed here
/// "#);
///
///     // Tries to execute I/O operation
///     let result = (|| -> Result<_, MyError> {
///         let f = track_try!(std::fs::File::open("/path/to/non_existent_file"));
///         Ok(f)
///     })();
///     let error = result.err().unwrap();
///     let cause = error.concrete_cause::<std::io::Error>().unwrap();
///     assert_eq!(cause.kind(), std::io::ErrorKind::NotFound);
/// }
/// ```
///
/// `TrackableError` is cloneable if `K` is so.
///
/// ```no_run
/// #[macro_use]
/// extern crate trackable;
///
/// use trackable::Trackable;
/// use trackable::error::{Failed, ErrorKindExt};
///
/// fn main() {
///     let mut original = Failed.error();
///     original.assign_tracking_number();
///
///     let original = track!(original, "Hello `original`!");
///     let forked = original.clone();
///     let forked = track!(forked, "Hello `forked`!");
///
///     assert_eq!(format!("\n{}", original), r#"
/// Failed #4d6fdaeeb2cc39a2
/// HISTORY:
///   [0] at <anon>:11; Hello `original`!
/// "#);
///
///     assert_eq!(format!("\n{}", forked), r#"
/// Failed #4d6fdaeeb2cc39a2
/// HISTORY:
///   [0] at <anon>:11; Hello `original`!
///   [1] at <anon>:13; Hello `forked`!
/// "#);
/// }
/// ```
#[derive(Debug, Clone)]
pub struct TrackableError<K> {
    kind: K,
    cause: Option<Arc<BoxError>>,
    history: Option<History>,
    tracking_number: Option<TrackingNumber>,
}
impl<K: ErrorKind> TrackableError<K> {
    /// Makes a new `TrackableError` instance.
    pub fn new<E>(kind: K, cause: E) -> Self
        where E: Into<BoxError>
    {
        let history = Self::init_history(&kind);
        TrackableError {
            kind: kind,
            cause: Some(Arc::new(cause.into())),
            history: history,
            tracking_number: None,
        }
    }

    /// Makes a new `TrackableError` instance from `kind`.
    ///
    /// Note that the returning error has no cause.
    fn from_kind(kind: K) -> Self {
        let history = Self::init_history(&kind);
        TrackableError {
            kind: kind,
            cause: None,
            history: history,
            tracking_number: None,
        }
    }

    /// Makes a new `TrackableError` instance from `cause`.
    pub fn from_cause<E>(cause: E) -> Self
        where K: IntoTrackableError<E>
    {
        K::into_trackable_error(cause)
    }

    /// Returns the kind of this error.
    pub fn kind(&self) -> &K {
        &self.kind
    }

    /// Tries to return the cause of this error as a value of `T` type.
    ///
    /// If neither this error has a cause nor it is an `T` value,
    /// this method will return `None`.
    pub fn concrete_cause<T>(&self) -> Option<&T>
        where T: Error + 'static
    {
        self.cause.as_ref().and_then(|c| c.downcast_ref())
    }

    fn init_history(kind: &K) -> Option<History> {
        if kind.is_tracking_needed() {
            Some(History::new())
        } else {
            None
        }
    }
}
impl<K: ErrorKind> From<K> for TrackableError<K> {
    fn from(kind: K) -> Self {
        Self::from_kind(kind)
    }
}
impl<K: ErrorKind + Default> Default for TrackableError<K> {
    fn default() -> Self {
        Self::from_kind(K::default())
    }
}
impl<K: ErrorKind> fmt::Display for TrackableError<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.kind.display(f)?;
        if let Some(ref e) = self.cause {
            write!(f, " (cause; {})", e)?;
        }
        if let Some(n) = self.tracking_number() {
            write!(f, " #{}", n)?;
        }
        if let Some(ref h) = self.history {
            write!(f, "\n{}", h)?;
        }
        Ok(())
    }
}
impl<K: ErrorKind> Error for TrackableError<K> {
    fn description(&self) -> &str {
        self.kind.description()
    }
    fn cause(&self) -> Option<&Error> {
        if let Some(ref e) = self.cause {
            Some(&***e)
        } else {
            None
        }
    }
}
impl<K> Trackable for TrackableError<K> {
    type Event = Event;
    fn assign_tracking_number(&mut self) {
        if self.tracking_number.is_none() {
            self.tracking_number = Some(TrackingNumber::generate());
        }
    }
    fn tracking_number(&self) -> Option<TrackingNumber> {
        self.tracking_number
    }
    fn enable_tracking(mut self) -> Self
        where Self: Sized
    {
        if self.history.is_none() {
            self.history = Some(History::new());
        }
        self
    }
    fn disable_tracking(mut self) -> Self
        where Self: Sized
    {
        self.history = None;
        self
    }
    fn history(&self) -> Option<&History> {
        self.history.as_ref()
    }
    fn history_mut(&mut self) -> Option<&mut History> {
        self.history.as_mut()
    }
}
impl<T, K> Trackable for Result<T, TrackableError<K>> {
    type Event = Event;
    fn assign_tracking_number(&mut self) {
        self.as_mut().err().map(|t| t.assign_tracking_number());
    }
    fn tracking_number(&self) -> Option<TrackingNumber> {
        self.as_ref().err().and_then(|t| t.tracking_number())
    }
    fn enable_tracking(self) -> Self
        where Self: Sized
    {
        self.map_err(|t| t.enable_tracking())
    }
    fn disable_tracking(self) -> Self
        where Self: Sized
    {
        self.map_err(|t| t.disable_tracking())
    }
    fn history(&self) -> Option<&History> {
        self.as_ref().err().and_then(|t| t.history())
    }
    fn history_mut(&mut self) -> Option<&mut History> {
        self.as_mut().err().and_then(|t| t.history_mut())
    }
}

/// This trait allows to construct `TrackableError<Self>` via a conversion from `From`.
pub trait IntoTrackableError<From>: Sized {
    /// Converts from `From` to `TrackableError<Self>`.
    fn into_trackable_error(f: From) -> TrackableError<Self>;
}
impl<T> IntoTrackableError<TrackableError<T>> for T {
    fn into_trackable_error(e: TrackableError<T>) -> TrackableError<T> {
        e
    }
}
impl<K: ErrorKind> IntoTrackableError<K> for K {
    fn into_trackable_error(kind: K) -> TrackableError<K> {
        kind.into()
    }
}

/// An event that occurred on an instance of `TrackableError`.
#[derive(Debug, Clone)]
pub enum Event {
    /// The location was saved in the history of error instance.
    Track(Location),

    /// The old error instance with the kind `BoxErrorKind` was taken over.
    TakeOver(Arc<BoxErrorKind>),
}
impl fmt::Display for Event {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Event::Track(ref l) => write!(f, "{}", l)?,
            Event::TakeOver(ref k) => write!(f, "takes over from `{:?}`", k)?,
        }
        Ok(())
    }
}
impl From<Location> for Event {
    fn from(f: Location) -> Self {
        Event::Track(f)
    }
}
