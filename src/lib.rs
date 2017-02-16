extern crate rand;

use std::fmt;
use std::error;

#[macro_export]
macro_rules! fail_if {
    ($($expr:tt)*) => {
        track_assert_not!($($expr)*)
    }
}
#[macro_export]
macro_rules! fail_if_ne {
    ($a:expr, $b:expr, $e:expr) => {
        track_assert!($a == $b, $e)
    }
}

#[macro_export]
macro_rules! may_fail {
    ($expr:expr) => {
        track_err!($expr)
    }
}

#[macro_export]
macro_rules! track_assert_not {
    ($cond:expr, $kind:expr) => {
        {
            if $cond {
                let e = track_err!($kind);
                Err(e)
            } else {
                Ok(())
            }
        }
    };
    ($cond:expr, $kind:expr, $msg:expr) => {
        {
            if $cond {
                let e = track_err!($kind, $msg);
                 Err(e)
            } else {
                Ok(())
            }
        }
    };
    ($cond:expr, $kind:expr, $fmt:expr, $($arg:tt)*) => {
        {
            if $cond {
                let e = track_err!($kind, $fmt, $($arg)*);
                Err(e)
            } else {
                Ok(())
            }
        }
    }
}

#[macro_export]
macro_rules! track_assert {
    ($cond:expr, $kind:expr) => {
        {
            if ! $cond {
                let e = track_err!($kind);
                Err(e)
            } else {
                Ok(())
            }
        }
    };
    ($cond:expr, $kind:expr, $msg:expr) => {
        {
            if ! $cond {
                let e = track_err!($kind, $msg);
                 Err(e)
            } else {
                Ok(())
            }
        }
    };
    ($cond:expr, $kind:expr, $fmt:expr, $($arg:tt)*) => {
        {
            if ! $cond {
                let e = track_err!($kind, $fmt, $($arg)*);
                Err(e)
            } else {
                Ok(())
            }
        }
    }
}

// track_panic!
// track_take_over

#[macro_export]
macro_rules! track_err {
    ($expr:expr) => {
        {
            let mut value = $expr;
            let location = $crate::Location::new(module_path!(), file!(), line!(), String::new());
            {
                use $crate::Trackable;
                value.track_location(location);
            }
            value
        }
    };
    ($expr:expr, $message:expr) => {
        track_err!($expr, $message, )
    };
    ($expr:expr, $fmt:expr, $($arg:tt)*) => {
        {
            let mut value = $expr;
            let message = format!($fmt, $($arg)*);
            let location = $crate::Location::new(module_path!(), file!(), line!(), message);
            {
                use $crate::Trackable;
                value.track_location(location);
            }
            value
        }
    };
}

// #[macro_export]
// macro_rules! force_track_err {

pub type BoxError = Box<error::Error + Send + Sync>;

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct TrackingNumber(u64);
impl TrackingNumber {
    pub fn new() -> Self {
        TrackingNumber(rand::random())
    }
    pub fn as_u64(&self) -> u64 {
        self.0
    }
}
impl fmt::Display for TrackingNumber {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:08X}", self.0)
    }
}

pub trait ErrorKind: fmt::Debug {
    fn description(&self) -> &str {
        "An error"
    }
    fn display(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
    fn enable_tracking(&self) -> bool {
        true
    }
    fn is_tracking_needed(&self) -> bool {
        true
    }
    fn cause<E>(self, error: E) -> Error<Self>
        where Self: Sized,
              E: Into<BoxError>
    {
        Error::new(self, error.into())
    }
    fn take_over<K>(self, _from: Error<K>, _locatin: Location) -> Error<Self>
        where Self: Sized
    {
        panic!()
    }
}

pub trait Trackable {
    fn track_location(&mut self, location: Location);
    // pub fn is_tracking_enabled(&self) -> bool {
    //     self.history.is_some()
    // }

    // pub fn enable_tracking(&mut self) {
    //     if self.history.is_none() {
    //         self.history = Some(Trace::new());
    //     }
    // }

    // #[cfg(not(feature = "force-tracking"))]
    // pub fn disable_tracking(&mut self) {
    //     self.history = None;
    // }

    // #[cfg(feature = "force-tracking")]
    // pub fn disable_tracking(&mut self) {}
}
impl<K: ErrorKind> Trackable for Error<K> {
    fn track_location(&mut self, location: Location) {
        if let Some(ref mut t) = self.history {
            t.save_location(location);
        }
    }
}
// TODO
// impl<K: ErrorKind> Trackable for Option<Error<K>> {
//     fn track_location(&mut self, location: Location) {
//         if let Some(ref mut e) = *self {
//             e.track_location(location);
//         }
//     }
// }
impl<T, E: Trackable> Trackable for Result<T, E> {
    fn track_location(&mut self, location: Location) {
        if let Err(ref mut e) = *self {
            e.track_location(location);
        }
    }
}

#[derive(Debug, Clone)]
struct History(Vec<Location>);
impl History {
    pub fn new() -> Self {
        History(Vec::new())
    }
    pub fn save_location(&mut self, location: Location) {
        self.0.push(location);
    }
    pub fn locations(&self) -> &[Location] {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub struct Location {
    module_path: &'static str,
    file: &'static str,
    line: u32,
    message: String,
}
impl Location {
    pub fn new(module_path: &'static str, file: &'static str, line: u32, message: String) -> Self {
        Location {
            module_path: module_path,
            file: file,
            line: line,
            message: message,
        }
    }
    pub fn module_path(&self) -> &'static str {
        self.module_path
    }
    pub fn file(&self) -> &'static str {
        self.file
    }
    pub fn line(&self) -> u32 {
        self.line
    }
    pub fn message(&self) -> &str {
        &self.message
    }
}

#[derive(Debug)]
pub struct Error<K> {
    kind: K,
    cause: Option<BoxError>,
    history: Option<History>,
    tracking_number: Option<TrackingNumber>,
}
impl<K: ErrorKind> Error<K> {
    pub fn new<E>(kind: K, cause: E) -> Self
        where E: Into<BoxError>
    {
        let history = Self::init_history(&kind);
        Error {
            kind: kind,
            cause: Some(cause.into()),
            history: history,
            tracking_number: None,
        }
    }
    pub fn from_cause<E>(cause: E) -> Self
        where E: Into<BoxError>,
              K: Default
    {
        Error::new(K::default(), cause)
    }
    pub fn from_kind(kind: K) -> Self {
        let history = Self::init_history(&kind);
        Error {
            kind: kind,
            cause: None,
            history: history,
            tracking_number: None,
        }
    }
    // pub fn take_over<J>(kind: K, from: Error<J>) -> Self
    //     where J: Into<BoxErrorKind>
    // {
    //     let mut history = from.history;
    //     if let Some(ref mut history) = history {
    //         history.add(TrackItem::TakeOver(from.kind.into()));
    //     }
    //     Error {
    //         kind: kind,
    //         cause: from.cause,
    //         history: history,
    //         tracking_number: from.tracking_number,
    //     }
    // }

    pub fn assign_tracking_number(&mut self) -> TrackingNumber {
        if self.tracking_number.is_none() {
            self.tracking_number = Some(TrackingNumber::new());
        }
        self.tracking_number().unwrap()
    }
    pub fn tracking_number(&self) -> Option<TrackingNumber> {
        self.tracking_number
    }
    pub fn kind(&self) -> &K {
        &self.kind
    }
    pub fn kind_mut(&mut self) -> &mut K {
        &mut self.kind
    }

    pub fn caused_by<T: error::Error + 'static>(&self) -> Option<&T> {
        self.cause.as_ref().and_then(|c| c.downcast_ref())
    }

    pub fn caused_by_mut<T: error::Error + 'static>(&mut self) -> Option<&mut T> {
        self.cause.as_mut().and_then(|c| c.downcast_mut())
    }

    // TOOD: &History
    pub fn history(&self) -> &[Location] {
        self.history.as_ref().map_or(&[][..], |t| t.locations())
    }
    // TODO: take_history, take_cause, take_kind(where K: Default)

    pub fn is_tracking_enabled(&self) -> bool {
        self.history.is_some()
    }

    pub fn enable_tracking(&mut self) {
        if self.history.is_none() {
            self.history = Some(History::new());
        }
    }

    #[cfg(not(feature = "force-tracking"))]
    pub fn disable_tracking(&mut self) {
        self.history = None;
    }

    #[cfg(feature = "force-tracking")]
    pub fn disable_tracking(&mut self) {}

    #[cfg(not(feature = "force-tracking"))]
    fn init_history(kind: &K) -> Option<History> {
        if kind.is_tracking_needed() {
            Some(History::new())
        } else {
            None
        }
    }

    #[cfg(feature = "force-tracking")]
    fn init_history(_kind: &K) -> Option<History> {
        Some(History::new())
    }
}
impl<K: ErrorKind> From<K> for Error<K> {
    fn from(kind: K) -> Self {
        Error::from_kind(kind)
    }
}
impl<K: ErrorKind + Default> Default for Error<K> {
    fn default() -> Self {
        Error::from_kind(K::default())
    }
}
impl<K: ErrorKind> fmt::Display for Error<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.kind.display(f)?;
        if let Some(ref e) = self.cause {
            write!(f, " (caused by; {})", e)?;
        }
        if self.history.is_some() {
            writeln!(f, "")?;
            writeln!(f, "  TRACE:")?;
            for (i, l) in self.history().iter().enumerate() {
                write!(f, "    [{}] {}#{}:{}", i, l.module_path, l.file, l.line)?;
                if l.message.is_empty() {
                    writeln!(f, "")?;
                } else {
                    writeln!(f, "; {}", l.message)?;
                }
            }
        }
        Ok(())
    }
}
impl<K: ErrorKind> error::Error for Error<K> {
    fn description(&self) -> &str {
        self.kind.description()
    }
    fn cause(&self) -> Option<&error::Error> {
        if let Some(ref e) = self.cause {
            Some(&**e)
        } else {
            None
        }
    }
}
