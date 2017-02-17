extern crate rand;

use std::fmt;

pub mod error;
mod macros;

pub trait Trackable {
    type Event: From<Location>;
    fn track<F>(&mut self, f: F)
        where F: FnOnce() -> Self::Event
    {
        self.history_mut().map(|h| h.add(f()));
    }

    fn assign_tracking_number(&mut self);
    fn tracking_number(&self) -> Option<TrackingNumber>;
    fn in_tracking(&self) -> bool {
        self.history().is_some()
    }
    fn enable_tracking(self) -> Self where Self: Sized;
    fn disable_tracking(self) -> Self where Self: Sized;

    fn history(&self) -> Option<&History<Self::Event>>;
    fn history_mut(&mut self) -> Option<&mut History<Self::Event>>;
}
impl<T: Trackable> Trackable for Option<T> {
    type Event = T::Event;

    fn assign_tracking_number(&mut self) {
        self.as_mut().map(|t| t.assign_tracking_number());
    }
    fn tracking_number(&self) -> Option<TrackingNumber> {
        self.as_ref().and_then(|t| t.tracking_number())
    }
    fn enable_tracking(self) -> Self
        where Self: Sized
    {
        self.map(|t| t.enable_tracking())
    }
    fn disable_tracking(self) -> Self
        where Self: Sized
    {
        self.map(|t| t.disable_tracking())
    }
    fn history(&self) -> Option<&History<Self::Event>> {
        self.as_ref().and_then(|t| t.history())
    }
    fn history_mut(&mut self) -> Option<&mut History<Self::Event>> {
        self.as_mut().and_then(|t| t.history_mut())
    }
}
impl<T, K: error::ErrorKind> Trackable for Result<T, error::TrackableError<K>> {
    type Event = <error::TrackableError<K> as Trackable>::Event;
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
    fn history(&self) -> Option<&History<Self::Event>> {
        self.as_ref().err().and_then(|t| t.history())
    }
    fn history_mut(&mut self) -> Option<&mut History<Self::Event>> {
        self.as_mut().err().and_then(|t| t.history_mut())
    }
}

/// The tracking history of a target.
///
/// A history is a sequence of the tracked events.
///
/// # Examples
///
/// ```
/// use std::fmt::{Display, Formatter, Result};
/// use trackable::History;
///
/// struct Event(&'static str);
/// impl Display for Event {
///     fn fmt(&self, f: &mut Formatter) -> Result {
///         write!(f, "event: {}", self.0)
///     }
/// }
///
/// let mut history = History::new();
/// history.add(Event("foo"));
/// history.add(Event("bar"));
///
/// assert_eq!(format!("\n{}", history), r#"
/// HISTORY:
///   [0] event: foo
///   [1] event: bar
/// "#);
/// ```
#[derive(Debug)]
pub struct History<Event>(Vec<Event>);
impl<Event> History<Event> {
    /// Makes an empty history.
    pub fn new() -> Self {
        History(Vec::new())
    }

    /// Adds an event to the tail of this history.
    pub fn add(&mut self, event: Event) {
        self.0.push(event);
    }

    /// Returns the tracked events in this history.
    pub fn events(&self) -> &[Event] {
        &self.0[..]
    }
}
impl<Event: fmt::Display> fmt::Display for History<Event> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "HISTORY:")?;
        for (i, e) in self.events().iter().enumerate() {
            writeln!(f, "  [{}] {}", i, e)?;
        }
        Ok(())
    }
}

/// The location of interest in source code files.
///
/// Typically this is created in the macros which defined in this crate.
#[derive(Debug, Clone)]
pub struct Location {
    module_path: &'static str,
    file: &'static str,
    line: u32,
    message: String,
}
impl Location {
    /// Makes a new `Location` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use trackable::Location;
    ///
    /// let location = Location::new(module_path!(), file!(), line!(), "Hello".to_string());
    /// assert_eq!(location.message(), "Hello");
    /// ```
    pub fn new(module_path: &'static str, file: &'static str, line: u32, message: String) -> Self {
        Location {
            module_path: module_path,
            file: file,
            line: line,
            message: message,
        }
    }

    /// Gets the crate name of this location.
    pub fn crate_name(&self) -> &'static str {
        if let Some(end) = self.module_path.find(":") {
            &self.module_path[..end]
        } else {
            self.module_path
        }
    }

    /// Gets the module path of this location.
    pub fn module_path(&self) -> &'static str {
        self.module_path
    }

    /// Gets the file name of this location.
    pub fn file(&self) -> &'static str {
        self.file
    }

    /// Gets the line of this location.
    pub fn line(&self) -> u32 {
        self.line
    }

    /// Gets the message left at this location.
    pub fn message(&self) -> &str {
        &self.message
    }
}

/// Randomly generated tracking number.
///
/// This is provided to help identifying a tracking target object.
///
/// Note that the numbers are generated by `rand::random()` function,
/// thus it is not guaranteed to have strict uniqueness.
///
/// # Examples
///
/// ```no_run
/// use trackable::TrackingNumber;
///
/// let n0 = TrackingNumber::assign();
/// let n1 = TrackingNumber::assign();
///
/// // NOTE: The actual values will change every time the below code is executed.
/// assert_ne!(n0, n1);
/// assert_eq!(n0.to_string(), "91fe3f35b6022840");
/// assert_eq!(n1.to_string(), "3d1a76ec17fb838f");
/// ```
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct TrackingNumber(pub u64);
impl TrackingNumber {
    /// Creates a new tracking number.
    pub fn assign() -> Self {
        TrackingNumber(rand::random())
    }
}
impl fmt::Display for TrackingNumber {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:08x}", self.0)
    }
}
