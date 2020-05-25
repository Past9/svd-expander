use anyhow::Error as AnyhowError;
use std::{error::Error, fmt};

/// Convenience type for a result that may contain an `SvdExpanderError`.
pub type SvdExpanderResult<T> = std::result::Result<T, SvdExpanderError>;

/// Error struct for all errors thrown by this crate or the crates on which it depends.
#[derive(Debug)]
pub struct SvdExpanderError {
  /// Description of the error that occurred.
  pub details: String,
}
impl SvdExpanderError {
  pub(crate) fn new(msg: &str) -> SvdExpanderError {
    Self {
      details: msg.to_string(),
    }
  }
}
impl fmt::Display for SvdExpanderError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.details)
  }
}
impl Error for SvdExpanderError {
  fn description(&self) -> &str {
    &self.details
  }
}
impl From<std::io::Error> for SvdExpanderError {
  fn from(err: std::io::Error) -> Self {
    SvdExpanderError::new(&format!("std::io::Error {}", &err.to_string()))
  }
}
impl From<std::ffi::OsString> for SvdExpanderError {
  fn from(_: std::ffi::OsString) -> Self {
    SvdExpanderError::new("std::ffi::OsString Could not convert OS String to UTF-8 string.")
  }
}
impl From<AnyhowError> for SvdExpanderError {
  fn from(err: AnyhowError) -> Self {
    SvdExpanderError::new(&format!("anyhow::Error {:?}", err))
  }
}
impl From<regex::Error> for SvdExpanderError {
  fn from(err: regex::Error) -> Self {
    SvdExpanderError::new(&format!("anyhow::Error {:?}", err))
  }
}
