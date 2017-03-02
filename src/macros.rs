/// Tries to track the current [location](struct.Location.html) into the history of the `$target`.
///
/// `$target` must be evaluated to a value which implements [Trackable](trait.Trackable.html) trait.
///
/// If `$target.in_tracking()` is `false`, it will simply return the value of `$target` untouched.
///
/// # Examples
///
/// ```
/// # #[macro_use]
/// # extern crate trackable;
/// #
/// # fn main() {
/// use trackable::error::{Failed, ErrorKindExt};
///
/// // Makes a `TrackableError` value
/// let e = Failed.cause("something wrong");
/// let e = track!(e);
///
/// // `Result<_, TrackableError>` implements `Trackable`
/// let e: Result<(), _> = Err(e);
/// let e = track!(e, "This is a note about this location");
///
/// // `Option<T: Trackable>` implements `Trackable`
/// let e = Some(e);
/// let e = track!(e, "Hello {}", "World!");
///
/// assert_eq!(format!("\n{}", e.unwrap().err().unwrap()), r#"
/// Failed (cause; something wrong)
/// HISTORY:
///   [0] at <anon>:9
///   [1] at <anon>:13; This is a note about this location
///   [2] at <anon>:17; Hello World!
/// "#);
/// # }
/// ```
#[macro_export]
macro_rules! track {
    ($target:expr) => {
        {
            use $crate::Trackable;
            let mut target = $target;
            target.track(|| {
                let location = $crate::Location::new(
                    module_path!(), file!(), line!(), String::new());
                From::from(location)
            });
            target
        }
    };
    ($target:expr, $($format_arg:tt)+) => {
        {
            use $crate::Trackable;
            let mut target = $target;
            target.track(|| {
                let message = format!($($format_arg)+);
                let location = $crate::Location::new(module_path!(), file!(), line!(), message);
                From::from(location)
            });
            target
        }
    };
}

/// Error trackable variant of the standard `try!` macro.
///
/// Conceptually, `track_try!(expr)` is equivalent to the following code:
///
/// ```no_run
/// # #[macro_use]
/// # extern crate trackable;
/// # use trackable::error::{TrackableError as Error, ErrorKind as Kind};
/// #
/// # fn main() {}
/// # fn foo<T, E: Kind>(expr: Result<T, Error<E>>) -> Result<T, Error<E>> {
/// # let v =
/// expr.map_err(|e| {
///     // Converts to a trackable error.
///     let e = trackable::error::TrackableError::from_cause(e);
///
///     // Saves this location in the history of `e`.
///     track!(e)
/// })?;
/// # Ok(v)
/// # }
/// ```
///
/// Like `trace!` macro, it is also possible to leave a message in this location:
///
/// ```no_run
/// # #[macro_use]
/// # extern crate trackable;
/// # use trackable::error::{TrackableError as Error, ErrorKind as Kind};
/// #
/// # fn try_something<E: Kind>(arg: usize) -> Result<(), Error<E>> { panic!() }
/// # fn main() {}
/// # fn foo<E: Kind>() -> Result<(), Error<E>> {
/// let arg = 0;
/// track_try!(try_something(arg), "Failed; The value of `arg` was {:?}", arg);
/// # Ok(())
/// # }
/// ```
#[macro_export]
macro_rules! track_try {
    ($expr:expr $(, $arg:tt)*) => {
        match $expr {
            Err(e) => {
                let e = track!($crate::error::TrackableError::from_cause(e) $(, $arg)*);
                Err(e)?
            }
            Ok(v) => {
                v
            }
        }
    };
}

/// Error tracking macro for the types which have `map_err` method.
///
/// Unlink `track_try!` macro,
/// This does not require that the `expr` is evaluated to a `std::result::Result` value.
/// And it will not return from the current function, even if the value of `expr` is erroneous.
///
/// ```
/// # #![allow(dead_code)]
/// # #[macro_use]
/// # extern crate trackable;
/// # fn main() {
/// use trackable::error::Failure;
///
/// enum MyResult<E> {
///     Ok(usize),
///     Err(E),
/// }
/// impl<E> MyResult<E> {
///     fn map_err<F, T>(self, f: F) -> MyResult<T> where F: FnOnce(E) -> T {
///         match self {
///             MyResult::Err(e) => MyResult::Err(f(e)),
///             MyResult::Ok(v) => MyResult::Ok(v),
///         }
///     }
///     fn err(self) -> Option<E> {
///         if let MyResult::Err(e) = self { Some(e) } else { None }
///     }
/// }
///
/// let result = MyResult::Err("something wrong");
/// let result: MyResult<Failure> = track_err!(result);
/// let result: MyResult<Failure> = track_err!(result, "Hello World!");
///
/// let e = result.err().unwrap();
/// assert_eq!(format!("\n{}", e), r#"
/// Failed (cause; something wrong)
/// HISTORY:
///   [0] at <anon>:24
///   [1] at <anon>:25; Hello World!
/// "#);
/// # }
/// ```
#[macro_export]
macro_rules! track_err {
    ($expr:expr $(, $arg:tt)*) => {
        $expr.map_err(|e| track!($crate::error::TrackableError::from_cause(e) $(, $arg)*))
    };
}

/// Error trackable variant of the standard `assert!` macro.
///
/// This is a simple wrapper of the `track_panic!` macro.
/// It will call `track_panic!($error_kind, $($format_arg)+)` if `$cond` is evaluated to `false`.
///
/// # Examples
///
/// ```
/// # #[macro_use]
/// # extern crate trackable;
/// #
/// # fn main() {
/// use trackable::error::{Failed, Failure};
///
/// fn add_positive_f32(a: f32, b: f32) -> Result<f32, Failure> {
///     track_assert!(a > 0.0 && b > 0.0, Failed);
///     Ok(a + b)
/// }
///
/// let r = add_positive_f32(3.0, 2.0); // Ok
/// assert_eq!(r.ok(), Some(5.0));
///
/// let r = add_positive_f32(1.0, -2.0); // Err
/// assert!(r.is_err());
/// assert_eq!(format!("\n{}", r.err().unwrap()), r#"
/// Failed (cause; assertion failed: a > 0.0 && b > 0.0)
/// HISTORY:
///   [0] at <anon>:8
/// "#);
/// # }
/// ```
#[macro_export]
macro_rules! track_assert {
    ($cond:expr, $error_kind:expr) => {
        track_assert!($cond, $error_kind, "assertion failed: {}", stringify!($cond));
    };
    ($cond:expr, $error_kind:expr, $($format_arg:tt)+) => {
        if ! $cond {
            track_panic!($error_kind, $($format_arg)+);
        }
    };
}

/// Error trackable variant of the standard `assert_ne!` macro.
///
/// Conceptually, `track_assert_eq!(left, right, error_kind)` is equivalent to
/// `track_assert!(left == right, error_kind)`.
#[macro_export]
macro_rules! track_assert_eq {
    ($left:expr, $right:expr, $error_kind:expr) => {
        let left = $left;
        let right = $right;
        track_assert!(left == right, $error_kind,
                      "assertion failed: `(left == right)` (left: `{:?}`, right: `{:?}`)",
                      left, right);
    };
    ($left:expr, $right:expr, $error_kind:expr, $fmt:expr, $($arg:tt)*) => {
        let left = $left;
        let right = $right;
        track_assert!(
            left == right, $error_kind,
            concat!("assertion failed: `(left == right)` (left: `{:?}`, right: `{:?}`): ", $fmt),
            left, right, $($arg)*);
    };
}


/// Error trackable variant of the standard `assert_ne!` macro.
///
/// Conceptually, `track_assert_ne!(left, right, error_kind)` is equivalent to
/// `track_assert!(left != right, error_kind)`.
#[macro_export]
macro_rules! track_assert_ne {
    ($left:expr, $right:expr, $error_kind:expr) => {
        let left = $left;
        let right = $right;
        track_assert!(left != right, $error_kind,
                      "assertion failed: `(left != right)` (left: `{:?}`, right: `{:?}`)",
                      left, right);
    };
    ($left:expr, $right:expr, $error_kind:expr, $fmt:expr, $($arg:tt)*) => {
        let left = $left;
        let right = $right;
        track_assert!(
            left != right, $error_kind,
            concat!("assertion failed: `(left != right)` (left: `{:?}`, right: `{:?}`): ", $fmt),
            left, right, $($arg)*);
    };
}

/// Error trackable variant of the standard `panic!` macro.
///
/// This returns an `TrackableError` object as the result value of the calling function,
/// instead of aborting the current thread.
///
/// Conceptually, `track_panic!(error)` is equivalent to the following code:
///
/// ```
/// # #[macro_use]
/// # extern crate trackable;
/// #
/// # use trackable::error::{Failed, Failure};
/// # fn main() { let _ = foo(); }
/// # fn foo() -> Result<(), Failure> {
/// use trackable::Trackable;
/// use trackable::error::TrackableError;
///
/// # let error = Failed;
/// let e = TrackableError::from(error); // Converts to `TrackableError`
/// let e = track!(e);                   // Tracks this location
/// Err(e)?;                             // Returns from the current function
/// # Ok(())
/// # }
/// ```
///
/// # Examples
///
/// ```
/// # #[macro_use]
/// # extern crate trackable;
/// #
/// # fn main() {
/// use trackable::error::{Failed, Failure};
///
/// fn foo<F>(f: F) -> Result<(), Failure> where F: FnOnce() -> Result<(), Failure> { f() }
///
/// let e = foo(|| { track_panic!(Failed); Ok(()) }).err().unwrap();
/// assert_eq!(format!("\n{}", e), r#"
/// Failed
/// HISTORY:
///   [0] at <anon>:9
/// "#);
///
/// let e = foo(|| { track_panic!(Failed, "something {}", "wrong"); Ok(()) }).err().unwrap();
/// assert_eq!(format!("\n{}", e), r#"
/// Failed (cause; something wrong)
/// HISTORY:
///   [0] at <anon>:16
/// "#);
/// # }
/// ```
#[macro_export]
macro_rules! track_panic {
    ($error:expr) => {
        {
            use $crate::Trackable;
            let e = $crate::error::TrackableError::from($error);
            let e = track!(e);
            return Err(From::from(e));
        }
    };
    ($error_kind:expr, $($format_arg:tt)+) => {
        {
            use $crate::error::ErrorKindExt;
            let message = format!($($format_arg)+);
            track_panic!($error_kind.cause(message));
        }
    };
}

/// More human readable variant of the standard `Result::unwrap` method.
///
/// # Examples
///
/// ```no_run
/// #[macro_use]
/// extern crate trackable;
///
/// use trackable::error::{Failed, Failure, ErrorKindExt};
///
/// fn main() {
///    let result: Result<(), Failure> = Err(Failed.error());
///
///    // Following two expressions are conceptually equivalent.
///    result.clone().unwrap();
///    track_unwrap_result!(result.clone());
///
///    // `track_unwrap_result!()` can take additional arguments compatible to `format!()`.
///    result.clone().expect(&format!("Additional information: {}", "foo"));
///    track_unwrap_result!(result.clone(), "Additional information: {}", "foo");
/// }
/// ```
#[macro_export]
macro_rules! track_unwrap_result {
    ($expr:expr) => {
        match track!($expr) {
            Err(e) => { panic!("\nEXPRESSION: {}\nERROR: {}\n", stringify!($expr), e); }
            Ok(v) => { v }
        }
    };
    ($expr:expr, $($format_arg:tt)*) => {
        match track!($expr, $($format_arg)*) {
            Err(e) => { panic!("\nEXPRESSION: {}\nERROR: {}\n", stringify!($expr), e); }
            Ok(v) => { v }
        }
    };
}
