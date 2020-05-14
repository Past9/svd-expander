//! Expands arrays and resolves inheritance chains in CMSIS-SVD specifications.
//!
//! ## Example usage:
//!
//! ```rust
//! use svd_expander::DeviceSpec;
//!
//! fn main() {
//!   let xml = r##"
//!   <device>
//!     <name>CORTEX_DEVICE</name>
//!     <peripherals>
//!
//!       <peripheral>
//!         <name>GPIOA</name>
//!         <baseAddress>0x40010000</baseAddress>
//!         <registers>
//!           <register>
//!             <name>IDR</name>
//!             <description>Input Data Register</description>
//!             <addressOffset>0x00</addressOffset>
//!             <fields>
//!
//!               <!--
//!                 This field is a template that will be expanded
//!                 out to 16 input fields named D1 through D16.
//!               -->
//!
//!               <field>
//!                 <name>D%s</name>
//!                 <bitWidth>1</bitWidth>
//!                 <bitOffset>0</bitOffset>
//!                 <dim>16</dim>
//!                 <dimIndex>1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16</dimIndex>
//!                 <dimIncrement>1</dimIncrement>
//!               </field>
//!
//!             </fields>
//!           </register>
//!         </registers>
//!       </peripheral>
//!
//!       <!--
//!         GPIOA will be copied to make GPIOB below, which is identical
//!         except for any overridden properties (just name and
//!         baseAddress in this case).
//!       -->
//!
//!       <peripheral derivedFrom="GPIOA">
//!         <name>GPIOB</name>
//!         <baseAddress>0x40010100</baseAddress>
//!       </peripheral>
//!
//!     </peripherals>
//!   </device>
//!   "##;
//!
//!   let device = DeviceSpec::from_xml(xml).unwrap();
//!
//!   // The IDR register on GPIOA has been expanded to 16 fields.
//!   assert_eq!(16, device.get_register("GPIOA.IDR").unwrap().fields.len());
//!
//!   // Those fields each had their bit offset (location in the register)
//!   // incremented appropriately.
//!   assert_eq!(0, device.get_field("GPIOA.IDR.D1").unwrap().offset);
//!   assert_eq!(1, device.get_field("GPIOA.IDR.D2").unwrap().offset);
//!   // ...etc...
//!   assert_eq!(9, device.get_field("GPIOA.IDR.D10").unwrap().offset);
//!   // ...etc...
//!
//!   // GPIOB also has an IDR register with 16 fields, which was inherited
//!   // from GPIOA.
//!   assert_eq!(16, device.get_register("GPIOB.IDR").unwrap().fields.len());
//!
//!   // GPIOB kept its name and base address when it inherited properties
//!   // from GPIOA.
//!   assert_eq!("GPIOB", device.get_peripheral("GPIOB").unwrap().name);
//!   assert_eq!(
//!     0x40010100,
//!     device.get_peripheral("GPIOB").unwrap().base_address
//!   );
//! }
//! ```
//!
//! This crate is intended for use in code generators. It is under active development and bug
//! reports and feature requests are welcome.

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
pub use value::{
  EnumeratedValueSetSpec, EnumeratedValueSpec, EnumeratedValueUsageSpec, EnumeratedValueValueSpec,
  ModifiedWriteValuesSpec, WriteConstraintRangeSpec, WriteConstraintSpec,
};

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
