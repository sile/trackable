//! Functionalities for implementing trackable errors.
use std::fmt;
use std::error::Error;

use super::{TrackingNumber, Location, Trackable};

pub type BoxError = Box<Error + Send + Sync>;
pub type BoxErrorKind = Box<ErrorKind + Send + Sync>;

pub type History = ::History<Event>;

#[derive(Debug, Default, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Failed;
impl ErrorKind for Failed {}
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

pub type Failure = TrackableError<Failed>;

pub trait ErrorKindExt: ErrorKind {
    fn error<E>(cause: E) -> TrackableError<Self>
        where Self: IntoTrackableError<E>
    {
        Self::into_trackable_error(cause)
    }
    fn cause<E>(self, error: E) -> TrackableError<Self>
        where Self: Sized,
              E: Into<BoxError>
    {
        TrackableError::new(self, error.into())
    }
    fn takes_over<K>(self, from: TrackableError<K>) -> TrackableError<Self>
        where Self: Sized,
              K: ErrorKind + Into<BoxErrorKind>
    {
        let mut history = from.history;
        if let Some(ref mut h) = history {
            h.add(Event::TakeOver(from.kind.into()));
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

pub trait ErrorKind: fmt::Debug {
    fn description(&self) -> &str {
        "An error"
    }
    fn display(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
    fn is_tracking_needed(&self) -> bool {
        true
    }
}

#[derive(Debug)]
pub struct TrackableError<K> {
    kind: K,
    cause: Option<BoxError>,
    history: Option<History>,
    tracking_number: Option<TrackingNumber>,
}
impl<K: ErrorKind> TrackableError<K> {
    pub fn new<E>(kind: K, cause: E) -> Self
        where E: Into<BoxError>
    {
        let history = Self::init_history(&kind);
        TrackableError {
            kind: kind,
            cause: Some(cause.into()),
            history: history,
            tracking_number: None,
        }
    }
    fn from_kind(kind: K) -> Self {
        let history = Self::init_history(&kind);
        TrackableError {
            kind: kind,
            cause: None,
            history: history,
            tracking_number: None,
        }
    }
    pub fn kind(&self) -> &K {
        &self.kind
    }
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
            writeln!(f, "\n{}", h)?;
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
            Some(&**e)
        } else {
            None
        }
    }
}
impl<K: ErrorKind> Trackable for TrackableError<K> {
    type Event = Event;
    fn assign_tracking_number(&mut self) {
        if self.tracking_number.is_none() {
            self.tracking_number = Some(TrackingNumber::assign());
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

pub trait IntoTrackableError<From>: Sized {
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

#[derive(Debug)]
pub enum Event {
    Track(Location),
    TakeOver(BoxErrorKind),
}
impl fmt::Display for Event {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Event::Track(ref l) => {
                write!(f, "at {}:{}:{}", l.crate_name(), l.file(), l.line())?;
                if !l.message().is_empty() {
                    write!(f, "; {}", l.message())?;
                }
            }
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
