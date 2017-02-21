#[macro_use]
extern crate trackable;

use trackable::error::{TrackableError, IntoTrackableError, Failure};
use trackable::error::{ErrorKind as TrackableErrorKind, ErrorKindExt};

pub type Error = TrackableError<ErrorKind>;

#[derive(Debug, Clone)]
pub enum ErrorKind {
    Other,
}
impl TrackableErrorKind for ErrorKind {}
impl IntoTrackableError<Failure> for ErrorKind {
    fn into_trackable_error(from: Failure) -> Error {
        ErrorKind::Other.takes_over(from)
    }
}
impl IntoTrackableError<std::io::Error> for ErrorKind {
    fn into_trackable_error(from: std::io::Error) -> Error {
        ErrorKind::Other.cause(from)
    }
}

fn main() {
    let e = ErrorKind::Other.cause("something wrong");
    let e = track!(e);
    let e = track!(e);
    println!("Error: {}", e);
}
