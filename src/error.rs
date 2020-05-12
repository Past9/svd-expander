use anyhow::Error as AnyhowError;
use std::{error::Error, fmt};

pub type SvdExpanderResult<T> = std::result::Result<T, SvdExpanderError>;

#[derive(Debug)]
pub struct SvdExpanderError {
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
