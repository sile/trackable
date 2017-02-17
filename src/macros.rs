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
///     let e = trackable::error::ErrorKindExt::error(e);
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
                let e = track!($crate::error::ErrorKindExt::error(e) $(, $arg)*);
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
///   [0] at rust_out:<anon>:24
///   [1] at rust_out:<anon>:25; Hello World!
///
/// "#);
/// # }
/// ```
#[macro_export]
macro_rules! track_err {
    ($expr:expr $(, $arg:tt)*) => {
        $expr.map_err(|e| track!($crate::error::ErrorKindExt::error(e) $(, $arg)*))
    };
}

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

#[macro_export]
macro_rules! track_panic {
    ($error:expr) => {
        {
            use $crate::Trackable;
            let e = $crate::error::TrackableError::from($error).enable_tracking();
            let e = track!(e);
            Err(e)?;
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
