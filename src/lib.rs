use svd_parser::Access;

mod cluster;
mod device;
mod error;
mod field;
mod peripheral;
mod register;

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
