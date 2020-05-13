//! Expands arrays and resolves inheritance chains in CMSIS-SVD specifications.
//!
//! ## Example usage:
//!
//! ```no_run
//! use std::fs::File;
//! use std::io::Read;
//! use svd_expander::DeviceSpec;
//!
//! fn main() {
//!   let xml = &mut String::new();
//!
//!   File::open("./stm32f303.svd")
//!     .unwrap()
//!     .read_to_string(xml)
//!     .unwrap();
//!
//!   println!("{:#?}", DeviceSpec::from_xml(xml).unwrap());
//! }
//! ```
//!
//! This crate is intended for use in code generators. It is under active development and bug
//! reports are welcome.
//!
//! Feature requests may be considered, but [svd-expander](https://crates.io/crates/svd-expander)
//! depends on [svd-parser](https://crates.io/crates/svd-parser) (at least for now) to parse the
//! SVD files, so it can only implement the features supported by the parser.

use svd_parser::Access;

mod cluster;
mod device;
mod error;
mod field;
mod peripheral;
mod register;
mod value;

pub use cluster::ClusterSpec;
pub use device::{CpuSpec, DeviceSpec, EndianSpec};
pub use error::{SvdExpanderError, SvdExpanderResult};
pub use field::FieldSpec;
pub use peripheral::{AddressBlockSpec, InterruptSpec, PeripheralSpec};
pub use register::RegisterSpec;

/// Defines access rights for fields on the device, though it may be specified at a
/// higher level than individual fields.
///
/// # Values
///
/// * `ReadOnly` = Read access is permitted. Write operations have an undefined effect.
/// * `ReadWrite` = Read and write accesses are permitted.
/// * `ReadWriteOnce` = Read access is always permitted. Only the first write after a reset will
/// affect the content. Following writes have an undefined effect.
/// * `WriteOnce` = Read operations have undefined results. Only the first write after a reset will
/// affect the content.
/// * `WriteOnly` = Read operations have an undefined result. Write access is permitted.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum AccessSpec {
  /// Read access is permitted. Write operations have an undefined effect.
  ReadOnly,

  /// Read and write accesses are permitted.
  ReadWrite,

  /// Read access is always permitted. Only the first write after a reset will affect the content.
  /// Following writes have an undefined effect.
  ReadWriteOnce,

  /// Read operations have undefined results. Only the first write after a reset will affect the
  /// content.
  WriteOnce,

  /// Read operations have an undefined result. Write access is permitted.
  WriteOnly,
}
impl AccessSpec {
  pub(crate) fn new(access: &Access) -> AccessSpec {
    match access {
      Access::ReadOnly => AccessSpec::ReadOnly,
      Access::ReadWrite => AccessSpec::ReadWrite,
      Access::ReadWriteOnce => AccessSpec::ReadWriteOnce,
      Access::WriteOnce => AccessSpec::WriteOnce,
      Access::WriteOnly => AccessSpec::WriteOnly,
    }
  }

  /// Whether the field is readable at least once.
  pub fn can_read(&self) -> bool {
    match self {
      AccessSpec::ReadOnly | AccessSpec::ReadWrite | AccessSpec::ReadWriteOnce => true,
      _ => false,
    }
  }

  /// Whether the field is writable at least once.
  pub fn can_write(&self) -> bool {
    match self {
      AccessSpec::ReadWrite
      | AccessSpec::ReadWriteOnce
      | AccessSpec::WriteOnce
      | AccessSpec::WriteOnly => true,
      _ => false,
    }
  }
}
