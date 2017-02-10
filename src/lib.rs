use std::fmt;
use std::error::Error;

#[macro_export]
macro_rules! failed {
    ($reason:expr) => {
        {
            let mut failure = $crate::Failure::new($reason);
            let location = $crate::Location::new(module_path!(), file!(), line!());
            failure.trace_mut().add_location(location);
            Err(failure)?;
        }
    };
    ($fmt:expr, $($arg:tt)*) => {
        {
            let reason = format!($fmt, $($arg)*);
            failed!(reason)
        }
    }
}

#[macro_export]
macro_rules! fail_if_err {
    ($expr:expr) => {
        $expr.map_err(|e| {
            let mut failure = $crate::Failure::new(e);
            let location = $crate::Location::new(module_path!(), file!(), line!());
            failure.trace_mut().add_location(location);
            failure
        })
    };
    ($expr:expr, $message:expr) => {
        fail_if_err!($expr, $message, )
    };
    ($expr:expr, $fmt:expr, $($arg:tt)*) => {
        $expr.map_err(|e| {
            let mut failure = $crate::Failure::new(e);
            let message = format!($fmt, $($arg)*);
            let location = $crate::Location::with_message(module_path!(), file!(), line!(), message);
            failure.trace_mut().add_location(location);
            failure
        })
    }
}

#[macro_export]
macro_rules! trace_failure {
    ($expr:expr) => {
        $expr.map_err(|mut e| {
            if let Some(f) = $crate::MaybeFailure::try_as_failure_mut(&mut e) {
                let location = $crate::Location::new(module_path!(), file!(), line!());
                f.trace_mut().add_location(location);
            }
            e
        })
    };
    ($expr:expr, $message:expr) => {
        trace_failure!($expr, $message, )
    };
    ($expr:expr, $fmt:expr, $($arg:tt)*) => {
        $expr.map_err(|mut e| {
            if let Some(f) = $crate::MaybeFailure::try_as_failure_mut(&mut e) {
                let message = format!($fmt, $($arg)*);
                let location = $crate::Location::with_message(module_path!(), file!(), line!(), message);
                f.trace_mut().add_location(location);                
            }
            e
        })
    }
}

pub trait MaybeFailure {
    fn try_as_failure_mut(&mut self) -> Option<&mut Failure>;
}
impl MaybeFailure for Failure {
    fn try_as_failure_mut(&mut self) -> Option<&mut Failure> {
        Some(self)
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
