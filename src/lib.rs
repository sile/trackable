use std::fmt;
use std::error::Error;

#[macro_export]
macro_rules! failed {
    ($reason:expr) => {
        let location = $crate::Location::new(module_path!(), file!(), line!());
        let failure = $crate::Failure::with_location($reason, location);
        Err(failure)?
    };
    ($fmt:expr, $($arg:tt)*) => {
        let reason = format!($fmt, $($arg)*);
        failed!(reason)
    }
}

#[macro_export]
macro_rules! may_fail {
    ($expr:expr) => {
        $expr.map_err(|mut e| {
            $crate::MaybeFailure::save_location_if_failure(&mut e, || {
                $crate::Location::new(module_path!(), file!(), line!())
            });
            e
        })
    };
    ($expr:expr, $message:expr) => {
        may_fail!($expr, $message, )
    };
    ($expr:expr, $fmt:expr, $($arg:tt)*) => {
        $expr.map_err(|mut e| {
            $crate::MaybeFailure::save_location_if_failure(&mut e, || {
                let message = format!($fmt, $($arg)*);
                $crate::Location::with_message(module_path!(), file!(), line!(), message)
            });
            e
        })
    }
}

#[macro_export]
macro_rules! map_err_to_failure {
    ($expr:expr) => {
        $expr.map_err(|e| {
            let location = $crate::Location::new(module_path!(), file!(), line!());
            $crate::Failure::with_location(e, location)
        })
    };
    ($expr:expr, $message:expr) => {
        map_err_to_failure!($expr, $message, )
    };
    ($expr:expr, $fmt:expr, $($arg:tt)*) => {
        $expr.map_err(|e| {
            let message = format!($fmt, $($arg)*);
            let location = $crate::Location::with_message(module_path!(), file!(), line!(), message);
            $crate::Failure::with_location(e, location)
        })
    }
}

#[macro_export]
macro_rules! ensure_err_to_be_failure {
    ($expr:expr) => {
        $expr.map_err(|e| {
            let location = $crate::Location::new(module_path!(), file!(), line!());
            let mut failure = $crate::MaybeFailure::into_failure(e);
            failure.trace_mut().add_location(location);
            failure
        })
    };
    ($expr:expr, $message:expr) => {
        ensure_err_to_be_failure!($expr, $message, )
    };
    ($expr:expr, $fmt:expr, $($arg:tt)*) => {
        $expr.map_err(|e| {
            let message = format!($fmt, $($arg)*);
            let location = $crate::Location::with_message(module_path!(), file!(), line!(), message);
            let mut failure = $crate::MaybeFailure::into_failure(e);
            failure.trace_mut().add_location(location);
            failure
        })
    }
}

pub trait MaybeFailure: Sized {
    fn try_as_failure_mut(&mut self) -> Option<&mut Failure>;
    fn save_location_if_failure<F>(&mut self, f: F) where F: FnOnce() -> Location {
        if let Some(failure) = self.try_as_failure_mut() {
            let location = f();
            failure.trace_mut().add_location(location);
        }
    }
    fn try_into_failure(self) -> Result<Failure, Self>;
    fn into_failure(self) -> Failure where Self: Into<Box<Error + Send + Sync>>{
        match self.try_into_failure() {
            Ok(f) => f,
            Err(e) => Failure::new(e)
        }
    }
}
impl MaybeFailure for Failure {
    fn try_as_failure_mut(&mut self) -> Option<&mut Failure> {
        Some(self)
    }
    fn try_into_failure(self) -> Result<Failure, Self> {
        Ok(self)
    }
}

#[derive(Debug)]
pub struct Failure {
    reason: Box<Error + Send + Sync>,
    trace: Trace,
}
impl Failure {
    pub fn new<E>(reason: E) -> Self
        where E: Into<Box<Error + Send + Sync>>
    {
        Failure {
            reason: reason.into(),
            trace: Trace(vec![]),
        }
    }
    pub fn with_location<E>(reason: E, location: Location) -> Self
        where E: Into<Box<Error + Send + Sync>>
    {
        Failure {
            reason: reason.into(),
            trace: Trace(vec![location]),
        }
    }
    pub fn reason(&self) -> &Error {
        &*self.reason
    }
    pub fn trace(&self) -> &Trace {
        &self.trace
    }
    pub fn trace_mut(&mut self) -> &mut Trace {
        &mut self.trace
    }
}
impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Failed; {}", self.reason)?;

        if !self.trace.locations().is_empty() {
            writeln!(f, "")?;
            writeln!(f, "  TRACE:")?;
            for (i, l) in self.trace.locations().iter().enumerate() {
                write!(f,
                       "    [{}] {}#{}:{}",
                       i,
                       l.module_path,
                       l.file,
                       l.line)?;
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
impl Error for Failure {
    fn cause(&self) -> Option<&Error> {
        self.reason.cause()
    }
    fn description(&self) -> &str {
        "Failed to do something"
    }
}

#[derive(Debug, Clone)]
pub struct Trace(Vec<Location>);
impl Trace {
    pub fn add_location(&mut self, location: Location) {
        self.0.push(location);
    }
    pub fn locations(&self) -> &[Location] {
        &self.0
    }
    pub fn truncate(&mut self, len: usize) {
        self.0.truncate(len);
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
    pub fn with_message(module_path: &'static str,
                        file: &'static str,
                        line: u32,
                        message: String)
                        -> Self {
        Location {
            module_path: module_path,
            file: file,
            line: line,
            message: message,
        }
    }
    pub fn new(module_path: &'static str, file: &'static str, line: u32) -> Self {
        Self::with_message(module_path, file, line, String::new())
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

#[cfg(test)]
mod tests;
