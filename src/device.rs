use super::{peripheral::PeripheralSpec, AccessSpec, ClusterSpec, FieldSpec, RegisterSpec};
use crate::error::{Result, SvdExpanderError};
use svd_parser::{Cpu, Device, Endian};

#[derive(Debug, Clone, PartialEq)]
pub enum EndianSpec {
  Little,
  Big,
  Selectable,
  Other,
}
impl EndianSpec {
  pub fn new(e: &Endian) -> Self {
    match e {
      Endian::Little => EndianSpec::Little,
      Endian::Big => EndianSpec::Big,
      Endian::Selectable => EndianSpec::Selectable,
      Endian::Other => EndianSpec::Other,
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CpuSpec {
  pub name: String,
  pub revision: String,
  pub endian: EndianSpec,
  pub mpu_present: bool,
  pub fpu_present: bool,
  pub nvic_priority_bits: u32,
  pub has_vendor_systick: bool,
}
impl CpuSpec {
  pub fn new(c: &Cpu) -> Self {
    Self {
      name: c.name.clone(),
      revision: c.revision.clone(),
      endian: EndianSpec::new(&c.endian),
      mpu_present: c.mpu_present,
      fpu_present: c.fpu_present,
      nvic_priority_bits: c.nvic_priority_bits,
      has_vendor_systick: c.has_vendor_systick,
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct DeviceSpec {
  pub name: String,
  pub version: Option<String>,
  pub description: Option<String>,
  pub address_unit_bits: Option<u32>,
  pub width: Option<u32>,
  pub cpu: Option<CpuSpec>,
  pub peripherals: Vec<PeripheralSpec>,
  pub default_register_size: Option<u32>,
  pub default_register_reset_value: Option<u32>,
  pub default_register_reset_mask: Option<u32>,
  pub default_register_access: Option<AccessSpec>,
}
impl DeviceSpec {
  pub fn from_xml(xml: &str) -> Result<Self> {
    Ok(Self::new(&svd_parser::parse(xml)?)?)
  }

  pub fn new(d: &Device) -> Result<Self> {
    let mut device = Self {
      name: d.name.clone(),
      version: d.version.clone(),
      description: d.description.clone(),
      address_unit_bits: d.address_unit_bits.clone(),
      width: d.width.clone(),
      cpu: match d.cpu {
        Some(ref c) => Some(CpuSpec::new(c)),
        None => None,
      },
      peripherals: d
        .peripherals
        .iter()
        .map(|p| PeripheralSpec::new(p))
        .collect::<Result<Vec<PeripheralSpec>>>()?,
      default_register_reset_value: d.default_register_properties.reset_value,
      default_register_reset_mask: d.default_register_properties.reset_mask,
      default_register_size: d.default_register_properties.size,
      default_register_access: match d.default_register_properties.access {
        Some(ref a) => Some(AccessSpec::new(a)),
        None => None,
      },
    };

    while device.expand_inherited()? {}

    while device.propagate_default_register_properties() {}

    Ok(device)
  }

  fn iter_clusters(&self) -> impl Iterator<Item = &ClusterSpec> {
    self.peripherals.iter().flat_map(|p| p.iter_clusters())
  }

  fn iter_registers(&self) -> impl Iterator<Item = &RegisterSpec> {
    self.peripherals.iter().flat_map(|p| p.iter_registers())
  }

  fn iter_fields(&self) -> impl Iterator<Item = &FieldSpec> {
    self.peripherals.iter().flat_map(|p| p.iter_fields())
  }

  fn get_peripheral(&self, path: &str) -> Result<&PeripheralSpec> {
    match self.peripherals.iter().find(|p| p.path() == path) {
      Some(p) => Ok(p),
      None => Err(SvdExpanderError::new(&format!(
        "No peripheral at path '{}'",
        path
      ))),
    }
  }

  fn get_cluster(&self, path: &str) -> Result<&ClusterSpec> {
    match self.iter_clusters().find(|c| c.path() == path) {
      Some(c) => Ok(c),
      None => Err(SvdExpanderError::new(&format!(
        "No cluster at path '{}'",
        path
      ))),
    }
  }

  fn get_register(&self, path: &str) -> Result<&RegisterSpec> {
    match self.iter_registers().find(|r| r.path() == path) {
      Some(r) => Ok(r),
      None => Err(SvdExpanderError::new(&format!(
        "No register at path '{}'",
        path
      ))),
    }
  }

  fn get_field(&self, path: &str) -> Result<&FieldSpec> {
    match self.iter_fields().find(|f| f.path() == path) {
      Some(r) => Ok(r),
      None => Err(SvdExpanderError::new(&format!(
        "No fields at path '{}'",
        path
      ))),
    }
  }

  fn expand_inherited(&mut self) -> Result<bool> {
    let reference_device = self.clone();

    let mut changed = false;

    for peripheral in self.peripherals.iter_mut() {
      if peripheral.mutate_fields(|f| {
        let mut field_changed = false;
        if let Some(ref derived_from) = f.derived_from_path() {
          if f.inherit_from(reference_device.get_field(derived_from)?) {
            field_changed = true;
          }
        }
        Ok(field_changed)
      })? {
        changed = true;
      }
    }

    for peripheral in self.peripherals.iter_mut() {
      if peripheral.mutate_registers(|r| {
        let mut register_changed = false;
        if let Some(ref derived_from) = r.derived_from_path() {
          if r.inherit_from(reference_device.get_register(derived_from)?) {
            register_changed = true;
          }
        }
        Ok(register_changed)
      })? {
        changed = true;
      }
    }

    for peripheral in self.peripherals.iter_mut() {
      if peripheral.mutate_clusters(|c| {
        let mut cluster_changed = false;
        if let Some(ref derived_from) = c.derived_from_path() {
          if c.inherit_from(reference_device.get_cluster(derived_from)?) {
            cluster_changed = true;
          }
        }
        Ok(cluster_changed)
      })? {
        changed = true;
      }
    }

    for peripheral in self.peripherals.iter_mut() {
      if let Some(ref derived_from) = peripheral.derived_from_path() {
        if peripheral.inherit_from(reference_device.get_peripheral(derived_from)?) {
          changed = true;
        }
      }
    }

    Ok(changed)
  }

  fn propagate_default_register_properties(&mut self) -> bool {
    let mut changed = false;

    for peripheral in self.peripherals.iter_mut() {
      if peripheral.propagate_default_register_properties(
        self.default_register_size,
        self.default_register_reset_value,
        self.default_register_reset_mask,
        self.default_register_access,
      ) {
        changed = true;
      }
    }

    return changed;
  }
}

#[cfg(test)]
mod tests {
  use super::{DeviceSpec, EndianSpec};
  use crate::AccessSpec;
  use svd_parser::{parse::Parse, Device};
  use xmltree::Element;

  #[test]
  fn can_create_from_xml() {
    let el: Element = Element::parse(
      r##"
      <device>
        xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" schemaVersion="1.1" xsi:noNamespaceSchemaLocation="CMSIS-SVD_Schema_1_1.xsd">

        <name>FOO</name>
        <version>1.2</version>
        <description>Quux</description>
        <addressUnitBits>32</addressUnitBits>
        <width>16</width>

        <size>24</size>
        <resetValue>1234</resetValue>
        <resetMask>4321</resetMask>
        <access>read-write</access>

        <cpu>
          <name>BAR</name>
          <revision>1.3</revision>
          <endian>little</endian>
          <mpuPresent>true</mpuPresent>
          <fpuPresent>true</fpuPresent>
          <nvicPrioBits>4</nvicPrioBits>
          <vendorSystickConfig>true</vendorSystickConfig>
        </cpu>
  
        <peripherals>
          <peripheral>
            <name>P1</name>
            <baseAddress>3000</baseAddress>
          </peripheral>
          <peripheral>
            <name>P2</name>
            <baseAddress>4000</baseAddress>
          </peripheral>
        </peripherals>
      </device>
      "##
        .as_bytes(),
    )
    .unwrap();

    let di = Device::parse(&el).unwrap();
    let ds = DeviceSpec::new(&di).unwrap();

    assert_eq!("FOO", ds.name);
    assert_eq!("1.2", ds.version.unwrap());
    assert_eq!("Quux", ds.description.unwrap());
    assert_eq!(32, ds.address_unit_bits.unwrap());

    // The current version of svd-parser always parses width as None. If the dependency
    // is ever upgraded to a version where this is fixed, is it should equal Some(16) and
    // this test will fail. It should be updated to reflect the fix at that time.
    assert!(ds.width.is_none());

    assert_eq!(24, ds.default_register_size.unwrap());
    assert_eq!(1234, ds.default_register_reset_value.unwrap());
    assert_eq!(4321, ds.default_register_reset_mask.unwrap());
    assert_eq!(AccessSpec::ReadWrite, ds.default_register_access.unwrap());

    assert_eq!("BAR", ds.cpu.clone().unwrap().name);
    assert_eq!("1.3", ds.cpu.clone().unwrap().revision);
    assert_eq!(EndianSpec::Little, ds.cpu.clone().unwrap().endian);
    assert_eq!(true, ds.cpu.clone().unwrap().mpu_present);
    assert_eq!(true, ds.cpu.clone().unwrap().fpu_present);
    assert_eq!(4, ds.cpu.clone().unwrap().nvic_priority_bits);
    assert_eq!(true, ds.cpu.clone().unwrap().has_vendor_systick);

    assert_eq!(2, ds.peripherals.len());

    assert_eq!("P1", ds.peripherals[0].name);
    assert_eq!(3000, ds.peripherals[0].base_address);

    assert_eq!("P2", ds.peripherals[1].name);
    assert_eq!(4000, ds.peripherals[1].base_address);
  }
}
