use svd_parser::Access;

mod cluster;
mod device;
mod error;
mod field;
mod peripheral;
mod register;

pub use cluster::ClusterSpec;
pub use device::{CpuSpec, DeviceSpec, EndianSpec};
pub use error::{Result, SvdExpanderError};
pub use field::FieldSpec;
pub use peripheral::{AddressBlockSpec, InterruptSpec, PeripheralSpec};
pub use register::RegisterSpec;

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum AccessSpec {
  ReadOnly,
  ReadWrite,
  ReadWriteOnce,
  WriteOnce,
  WriteOnly,
}
impl AccessSpec {
  pub fn new(access: &Access) -> AccessSpec {
    match access {
      Access::ReadOnly => AccessSpec::ReadOnly,
      Access::ReadWrite => AccessSpec::ReadWrite,
      Access::ReadWriteOnce => AccessSpec::ReadWriteOnce,
      Access::WriteOnce => AccessSpec::WriteOnce,
      Access::WriteOnly => AccessSpec::WriteOnly,
    }
  }

  pub fn can_read(&self) -> bool {
    match self {
      AccessSpec::ReadOnly | AccessSpec::ReadWrite | AccessSpec::ReadWriteOnce => true,
      _ => false,
    }
  }

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
