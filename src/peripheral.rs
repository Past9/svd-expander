use super::{cluster::ClusterSpec, register::RegisterSpec, AccessSpec, FieldSpec};
use crate::{error::SvdExpanderResult};
use svd_parser::{AddressBlock, Interrupt, Peripheral, RegisterCluster};

/// Describes an address range uniquely mapped to a peripheral. 
#[derive(Debug, Clone, PartialEq)]
pub struct AddressBlockSpec {
  /// The start address of the address block relative to the peripheral's base address.
  pub offset: u32,

  /// The number of address unit bits covered by this address block. The end of an address block is
  /// the sum of the peripheral's base address and the address block's offset and size.
  pub size: u32,

  /// What the address block is used for. The following predefined values are expected:
  /// * `registers`
  /// * `buffer`
  /// * `reserved`
  pub usage: String,
}
impl AddressBlockSpec {
  pub(crate) fn new(ab: &AddressBlock) -> Self {
    Self {
      offset: ab.offset,
      size: ab.size,
      usage: ab.usage.clone(),
    }
  }
}

/// Describes an interrupt that exists on a peripheral.
#[derive(Debug, Clone, PartialEq)]
pub struct InterruptSpec {
  /// The unique name of the interrupt.
  pub name: String,

  /// Overview of the interrupt's purpose and function.
  pub description: Option<String>,

  /// The index value of the interrupt.
  pub value: u32,
}
impl InterruptSpec {
  pub(crate) fn new(is: &Interrupt) -> Self {
    Self {
      name: is.name.clone(),
      description: is.description.clone(),
      value: is.value,
    }
  }

  pub(crate) fn inherit_from(&mut self, is: &InterruptSpec) -> bool {
    let mut changed = false;

    if self.description.is_none() && is.description.is_some() {
      self.description = is.description.clone();
      changed = true;
    }

    changed
  }
}

/// Describes a peripheral on a device.
#[derive(Debug, Clone, PartialEq)]
pub struct PeripheralSpec {
  derived_from: Option<String>,

  /// Name of the peripheral. Must be unique for the entire device.
  pub name: String,

  /// The version of the peripheral description.
  pub version: Option<String>,

  /// Human-friendly name of the peripheral.
  pub display_name: Option<String>,

  /// Name of the group to which this peripheral belongs. This is optional and is mostly
  /// intended to visually group the peripheral with related peripherals in documentation 
  /// and user interfaces.
  pub group_name: Option<String>,

  /// Overview of the purpose and functionality of the peripheral.
  pub description: Option<String>,

  /// Lowest address reserved or used by the peripheral.
  pub base_address: u32,

  /// An address range uniquely mapped to this peripheral. 
  pub address_block: Option<AddressBlockSpec>,

  /// Default bit-width of any register contained in this peripheral.
  pub default_register_size: Option<u32>,

  /// Default value after reset of any register contained in this peripheral.
  pub default_register_reset_value: Option<u32>,

  /// Default register bits that have a defined reset value for any register in this peripheral.
  pub default_register_reset_mask: Option<u32>,

  /// Default access rights for any register contained in this peripheral.
  pub default_register_access: Option<AccessSpec>,

  /// Interrupts that exist on this peripheral.
  pub interrupts: Vec<InterruptSpec>,

  /// Top-level registers that exist on this peripheral.
  pub registers: Vec<RegisterSpec>,

  /// Top-level register clusters that exist on this peripheral. Clusters may contain registers
  /// or other clusters.  
  pub clusters: Vec<ClusterSpec>,
}
impl PeripheralSpec {
  pub(crate) fn new(p: &Peripheral) -> SvdExpanderResult<Self> {
    let mut peripheral = Self {
      derived_from: p.derived_from.clone(),
      name: p.name.clone(),
      version: p.version.clone(),
      display_name: p.display_name.clone(),
      group_name: p.group_name.clone(),
      description: p.description.clone(),
      base_address: p.base_address,
      address_block: match p.address_block {
        Some(ref ab) => Some(AddressBlockSpec::new(ab)),
        None => None,
      },
      default_register_size: p.default_register_properties.size,
      default_register_reset_value: p.default_register_properties.reset_value,
      default_register_reset_mask: p.default_register_properties.reset_mask,
      default_register_access: match p.default_register_properties.access {
        Some(ref a) => Some(AccessSpec::new(a)),
        None => None,
      },
      interrupts: p.interrupt.iter().map(|i| InterruptSpec::new(i)).collect(),
      registers: Vec::with_capacity(0),
      clusters: Vec::with_capacity(0),
    };

    peripheral.registers = match p.registers {
      Some(ref register_clusters) => {
        let mut registers = Vec::new();
        for register in register_clusters.iter().filter_map(|rc| match rc {
          RegisterCluster::Register(ref r) => Some(r),
          RegisterCluster::Cluster(_) => None
        }) {
          registers.extend(RegisterSpec::new(register, &peripheral.name)?);
        }
        registers
      },
      None => Vec::new()
    };

    peripheral.clusters = match p.registers {
      Some(ref register_clusters) => {
        let mut clusters = Vec::new();
        for cluster in register_clusters.iter().filter_map(|rc| match rc {
          RegisterCluster::Cluster(ref c) => Some(c),
          RegisterCluster::Register(_) => None
        }) {
          clusters.extend(ClusterSpec::new(cluster, &peripheral.name)?);
        }
        clusters
      },
      None => Vec::new()
    };

    Ok(peripheral)
  }

  /// Recursively iterates all the register clusters contained within this peripheral.
  pub fn iter_clusters(&self) -> impl Iterator<Item = &ClusterSpec> {
    self.clusters.iter().flat_map(|c| c.iter_clusters())
  }

  /// Recursively iterates all the registers contained within this peripheral.
  pub fn iter_registers(&self) -> impl Iterator<Item = &RegisterSpec> {
    self
      .clusters
      .iter()
      .flat_map(|c| c.iter_registers())
      .chain(self.registers.iter())
  }

  /// Recursively iterates all the register fields contained within this peripheral.
  pub fn iter_fields(&self) -> impl Iterator<Item = &FieldSpec> {
    self
      .clusters
      .iter()
      .flat_map(|c| c.iter_fields())
      .chain(self.registers.iter().flat_map(|r| r.fields.iter()))
  }

  /// The full path of the peripheral that this peripheral inherits from (if any).
  /// Since all peripherals are top-level components of the device, this is just the
  /// name of the other peripheral.
  pub fn derived_from_path(&self) -> Option<String> {
    self.derived_from.clone()
  }

  /// The full path of this peripheral. Since all peripherals are top-level components of the
  /// device, this is just the name of the peripheral. 
  pub fn path(&self) -> String {
    self.name.clone()
  }

  pub(crate) fn mutate_clusters<F>(&mut self, f: F) -> SvdExpanderResult<bool>
  where
    F: Fn(&mut ClusterSpec) -> SvdExpanderResult<bool>,
    F: Copy,
  {
    let mut changed = false;

    for child in &mut self.clusters.iter_mut() {
      if child.mutate_clusters(f)? {
        changed = true;
      }
    }

    Ok(changed)
  }

  pub(crate) fn mutate_registers<F>(&mut self, f: F) -> SvdExpanderResult<bool>
  where
    F: Fn(&mut RegisterSpec) -> SvdExpanderResult<bool>,
    F: Copy,
  {
    let mut changed = false;

    for cluster in &mut self.clusters.iter_mut() {
      if cluster.mutate_registers(f)? {
        changed = true;
      }
    }

    for register in self.registers.iter_mut() {
      if f(register)? {
        changed = true;
      }
    }

    Ok(changed)
  }

  pub(crate) fn mutate_fields<F>(&mut self, f: F) -> SvdExpanderResult<bool>
  where
    F: Fn(&mut FieldSpec) -> SvdExpanderResult<bool>,
    F: Copy,
  {
    let mut changed = false;

    for cluster in &mut self.clusters.iter_mut() {
      if cluster.mutate_fields(f)? {
        changed = true;
      }
    }

    for register in &mut self.registers.iter_mut() {
      if register.mutate_fields(f)? {
        changed = true;
      }
    }

    Ok(changed)
  }

  pub(crate) fn inherit_from(&mut self, ps: &PeripheralSpec) -> bool {
    let mut changed = false;

    if self.version.is_none() && ps.version.is_some() {
      self.version = ps.version.clone();
      changed = true;
    }

    if self.display_name.is_none() && ps.display_name.is_some() {
      self.display_name = ps.display_name.clone();
      changed = true;
    }

    if self.group_name.is_none() && ps.group_name.is_some() {
      self.group_name = ps.group_name.clone();
      changed = true;
    }

    if self.description.is_none() && ps.description.is_some() {
      self.description = ps.description.clone();
      changed = true;
    }

    if self.address_block.is_none() && ps.address_block.is_some() {
      self.address_block = ps.address_block.clone();
      changed = true;
    }

    if self.default_register_size.is_none() && ps.default_register_size.is_some() {
      self.default_register_size = ps.default_register_size;
      changed = true;
    }

    if self.default_register_reset_value.is_none() && ps.default_register_reset_value.is_some() {
      self.default_register_reset_value = ps.default_register_reset_value;
      changed = true;
    }

    if self.default_register_reset_mask.is_none() && ps.default_register_reset_mask.is_some() {
      self.default_register_reset_mask = ps.default_register_reset_mask;
      changed = true;
    }

    if self.default_register_access.is_none() && ps.default_register_access.is_some() {
      self.default_register_access = ps.default_register_access.clone();
      changed = true;
    }

    for ancestor in ps.interrupts.iter() {
      if let Some(ref mut descendant) = self.interrupts.iter_mut().find(|r| r.name == ancestor.name)
      {
        if descendant.inherit_from(ancestor) {
          changed = true;
        }
      } 
    }

    for ancestor in ps.registers.iter() {
      if let Some(ref mut descendant) = self.registers.iter_mut().find(|r| r.name == ancestor.name)
      {
        if descendant.inherit_from(ancestor) {
          changed = true;
        }
      } else {
        self
          .registers
          .push(ancestor.clone_with_preceding_path(&self.path()));
        changed = true;
      }
    }

    for ancestor in ps.clusters.iter() {
      if let Some(ref mut descendant) = self.clusters.iter_mut().find(|c| c.name == ancestor.name) {
        if descendant.inherit_from(ancestor) {
          changed = true;
        }
      } else {
        self
          .clusters
          .push(ancestor.clone_with_preceding_path(&self.path()));
        changed = true;
      }
    }

    changed
  }

  pub(crate) fn propagate_default_register_properties(
    &mut self,
    size: Option<u32>,
    reset_value: Option<u32>,
    reset_mask: Option<u32>,
    access: Option<AccessSpec>,
  ) -> bool {
    let mut changed = false;

    if self.default_register_size.is_none() && size.is_some() {
      self.default_register_size = size;
      changed = true;
    }

    if self.default_register_reset_value.is_none() && reset_value.is_some() {
      self.default_register_reset_value = reset_value;
      changed = true;
    }

    if self.default_register_reset_mask.is_none() && reset_mask.is_some() {
      self.default_register_reset_mask = reset_mask;
      changed = true;
    }

    if self.default_register_access.is_none() && access.is_some() {
      self.default_register_access = access;
      changed = true;
    }

    for cluster in self.clusters.iter_mut() {
      if cluster.propagate_default_register_properties(
        self.default_register_size,
        self.default_register_reset_value,
        self.default_register_reset_mask,
        self.default_register_access,
      ) {
        changed = true;
      }
    }

    for register in self.registers.iter_mut() {
      if register.propagate_default_register_properties(
        self.default_register_size,
        self.default_register_reset_value,
        self.default_register_reset_mask,
        self.default_register_access,
      ) {
        changed = true;
      }
    }

    changed
  }
}

#[cfg(test)]
mod tests {
  use super::PeripheralSpec;
  use crate::{AccessSpec, ClusterSpec, RegisterSpec};
  use std::cell::RefCell;
  use svd_parser::{parse::Parse, Peripheral};
  use xmltree::Element;

  #[test]
  fn can_create_from_xml() {
    let el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <version>1.2</version>
        <displayName>Bar</displayName>
        <groupName>Baz</groupName>
        <description>Quux</description>
        <baseAddress>3000</baseAddress>
        <access>write-only</access>
        <resetValue>1234</resetValue>
        <resetMask>4321</resetMask>
        <size>16</size>
        <addressBlock>
          <offset>0x200</offset>
          <size>1000</size>
          <usage>register</usage>
        </addressBlock>
        <interrupt>
          <name>I1</name>
          <description>Corge 1</description>
          <value>45</value>
        </interrupt>
        <interrupt>
          <name>I2</name>
          <description>Corge 2</description>
          <value>23</value>
        </interrupt>
        <registers>
          <register>
            <name>R1</name>
            <addressOffset>100</addressOffset>
          </register>
          <register>
            <name>R2</name>
            <addressOffset>200</addressOffset>
          </register>
          <cluster>
            <name>C1</name>
            <addressOffset>200</addressOffset>
          </cluster>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let pi = Peripheral::parse(&el).unwrap();

    let ps = PeripheralSpec::new(&pi).unwrap();

    assert_eq!("FOO", ps.name);
    assert_eq!("1.2", ps.version.unwrap());
    assert_eq!("Bar", ps.display_name.unwrap());
    assert_eq!("Baz", ps.group_name.unwrap());
    assert_eq!("Quux", ps.description.unwrap());
    assert_eq!(3000, ps.base_address);
    assert_eq!(AccessSpec::WriteOnly, ps.default_register_access.unwrap());
    assert_eq!(1234, ps.default_register_reset_value.unwrap());
    assert_eq!(4321, ps.default_register_reset_mask.unwrap());
    assert_eq!(16, ps.default_register_size.unwrap());
    assert_eq!(0x200, ps.address_block.clone().unwrap().offset);
    assert_eq!(1000, ps.address_block.clone().unwrap().size);
    assert_eq!("register", ps.address_block.clone().unwrap().usage);

    assert_eq!(2, ps.interrupts.len());

    assert_eq!("I1", ps.interrupts[0].name);
    assert_eq!("Corge 1", ps.interrupts[0].description.clone().unwrap());
    assert_eq!(45, ps.interrupts[0].value);

    assert_eq!("I2", ps.interrupts[1].name);
    assert_eq!("Corge 2", ps.interrupts[1].description.clone().unwrap());
    assert_eq!(23, ps.interrupts[1].value);

    assert_eq!(2, ps.registers.len());
    assert_eq!("R1", ps.registers[0].name);
    assert_eq!("R2", ps.registers[1].name);

    assert_eq!(1, ps.clusters.len());
    assert_eq!("C1", ps.clusters[0].name);
  }

  #[test]
  fn inherits_from_other_peripheral() {
    let descendant_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
        <interrupt>
          <name>I1</name>
          <value>45</value>
        </interrupt>
        <registers>
          <register>
            <name>R1</name>
            <addressOffset>100</addressOffset>
          </register>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_pi = Peripheral::parse(&descendant_el).unwrap();
    let mut descendant_ps = PeripheralSpec::new(&descendant_pi).unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO2</name>
        <version>1.2</version>
        <displayName>Bar</displayName>
        <groupName>Baz</groupName>
        <description>Quux</description>
        <baseAddress>4000</baseAddress>
        <access>write-only</access>
        <resetValue>1234</resetValue>
        <resetMask>4321</resetMask>
        <size>16</size>
        <addressBlock>
          <offset>0x200</offset>
          <size>1000</size>
          <usage>register</usage>
        </addressBlock>
        <interrupt>
          <name>I1</name>
          <description>Corge 1</description>
          <value>45</value>
        </interrupt>
        <interrupt>
          <name>I2</name>
          <description>Corge 2</description>
          <value>23</value>
        </interrupt>
        <registers>
          <register>
            <name>R1</name>
            <addressOffset>100</addressOffset>
          </register>
          <register>
            <name>R2</name>
            <addressOffset>200</addressOffset>
          </register>
          <cluster>
            <name>C1</name>
            <addressOffset>200</addressOffset>
          </cluster>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_pi = Peripheral::parse(&ancestor_el).unwrap();
    let ancestor_ps = PeripheralSpec::new(&ancestor_pi).unwrap();

    let changed = descendant_ps.inherit_from(&ancestor_ps);

    assert!(changed);

    assert_eq!("FOO", descendant_ps.name);
    assert_eq!("1.2", descendant_ps.version.unwrap());
    assert_eq!("Bar", descendant_ps.display_name.unwrap());
    assert_eq!("Baz", descendant_ps.group_name.unwrap());
    assert_eq!("Quux", descendant_ps.description.unwrap());
    assert_eq!(3000, descendant_ps.base_address);
    assert_eq!(
      AccessSpec::WriteOnly,
      descendant_ps.default_register_access.unwrap()
    );
    assert_eq!(1234, descendant_ps.default_register_reset_value.unwrap());
    assert_eq!(4321, descendant_ps.default_register_reset_mask.unwrap());
    assert_eq!(16, descendant_ps.default_register_size.unwrap());
    assert_eq!(0x200, descendant_ps.address_block.clone().unwrap().offset);
    assert_eq!(1000, descendant_ps.address_block.clone().unwrap().size);
    assert_eq!(
      "register",
      descendant_ps.address_block.clone().unwrap().usage
    );

    assert_eq!(1, descendant_ps.interrupts.len());

    assert_eq!("I1", descendant_ps.interrupts[0].name);
    assert_eq!(
      "Corge 1",
      descendant_ps.interrupts[0].description.clone().unwrap()
    );
    assert_eq!(45, descendant_ps.interrupts[0].value);

    assert_eq!(2, descendant_ps.registers.len());
    assert_eq!("R1", descendant_ps.registers[0].name);
    assert_eq!("R2", descendant_ps.registers[1].name);

    assert_eq!(1, descendant_ps.clusters.len());
    assert_eq!("C1", descendant_ps.clusters[0].name);
  }

  #[test]
  fn inherits_from_returns_false_when_no_changes() {
    let descendant_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <version>1.2</version>
        <displayName>Bar</displayName>
        <groupName>Baz</groupName>
        <description>Quux</description>
        <baseAddress>3000</baseAddress>
        <access>write-only</access>
        <resetValue>1234</resetValue>
        <resetMask>4321</resetMask>
        <size>16</size>
        <addressBlock>
          <offset>0x200</offset>
          <size>1000</size>
          <usage>register</usage>
        </addressBlock>
        <interrupt>
          <name>I1</name>
          <description>Corge 1</description>
          <value>45</value>
        </interrupt>
        <interrupt>
          <name>I2</name>
          <description>Corge 2</description>
          <value>23</value>
        </interrupt>
        <registers>
          <register>
            <name>R1</name>
            <addressOffset>100</addressOffset>
          </register>
          <register>
            <name>R2</name>
            <addressOffset>200</addressOffset>
          </register>
          <cluster>
            <name>C1</name>
            <addressOffset>200</addressOffset>
          </cluster>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_pi = Peripheral::parse(&descendant_el).unwrap();
    let mut descendant_ps = PeripheralSpec::new(&descendant_pi).unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO2</name>
        <version>1.2</version>
        <displayName>Bar</displayName>
        <groupName>Baz</groupName>
        <description>Quux</description>
        <baseAddress>4000</baseAddress>
        <access>write-only</access>
        <resetValue>1234</resetValue>
        <resetMask>4321</resetMask>
        <size>16</size>
        <addressBlock>
          <offset>0x200</offset>
          <size>1000</size>
          <usage>register</usage>
        </addressBlock>
        <interrupt>
          <name>I1</name>
          <description>Corge 1</description>
          <value>45</value>
        </interrupt>
        <interrupt>
          <name>I2</name>
          <description>Corge 2</description>
          <value>23</value>
        </interrupt>
        <registers>
          <register>
            <name>R1</name>
            <addressOffset>100</addressOffset>
          </register>
          <register>
            <name>R2</name>
            <addressOffset>200</addressOffset>
          </register>
          <cluster>
            <name>C1</name>
            <addressOffset>200</addressOffset>
          </cluster>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_pi = Peripheral::parse(&ancestor_el).unwrap();
    let ancestor_ps = PeripheralSpec::new(&ancestor_pi).unwrap();

    let changed = descendant_ps.inherit_from(&ancestor_ps);

    assert!(!changed);

    assert_eq!("FOO", descendant_ps.name);
    assert_eq!("1.2", descendant_ps.version.unwrap());
    assert_eq!("Bar", descendant_ps.display_name.unwrap());
    assert_eq!("Baz", descendant_ps.group_name.unwrap());
    assert_eq!("Quux", descendant_ps.description.unwrap());
    assert_eq!(3000, descendant_ps.base_address);
    assert_eq!(
      AccessSpec::WriteOnly,
      descendant_ps.default_register_access.unwrap()
    );
    assert_eq!(1234, descendant_ps.default_register_reset_value.unwrap());
    assert_eq!(4321, descendant_ps.default_register_reset_mask.unwrap());
    assert_eq!(16, descendant_ps.default_register_size.unwrap());
    assert_eq!(0x200, descendant_ps.address_block.clone().unwrap().offset);
    assert_eq!(1000, descendant_ps.address_block.clone().unwrap().size);
    assert_eq!(
      "register",
      descendant_ps.address_block.clone().unwrap().usage
    );

    assert_eq!(2, descendant_ps.interrupts.len());

    assert_eq!("I1", descendant_ps.interrupts[0].name);
    assert_eq!(
      "Corge 1",
      descendant_ps.interrupts[0].description.clone().unwrap()
    );
    assert_eq!(45, descendant_ps.interrupts[0].value);

    assert_eq!("I2", descendant_ps.interrupts[1].name);
    assert_eq!(
      "Corge 2",
      descendant_ps.interrupts[1].description.clone().unwrap()
    );
    assert_eq!(23, descendant_ps.interrupts[1].value);

    assert_eq!(2, descendant_ps.registers.len());
    assert_eq!("R1", descendant_ps.registers[0].name);
    assert_eq!("R2", descendant_ps.registers[1].name);

    assert_eq!(1, descendant_ps.clusters.len());
    assert_eq!("C1", descendant_ps.clusters[0].name);
  }

  #[test]
  fn inherits_from_returns_true_for_overridden_inherited_interrupt() {
    let descendant_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
        <interrupt>
          <name>I1</name>
          <value>45</value>
        </interrupt>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_pi = Peripheral::parse(&descendant_el).unwrap();
    let mut descendant_ps = PeripheralSpec::new(&descendant_pi).unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO2</name>
        <baseAddress>4000</baseAddress>
        <interrupt>
          <name>I1</name>
          <description>Corge</description>
          <value>23</value>
        </interrupt>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_pi = Peripheral::parse(&ancestor_el).unwrap();
    let ancestor_ps = PeripheralSpec::new(&ancestor_pi).unwrap();

    let changed = descendant_ps.inherit_from(&ancestor_ps);

    assert!(changed);

    assert_eq!("FOO", descendant_ps.name);
    assert_eq!(3000, descendant_ps.base_address);

    assert_eq!(1, descendant_ps.interrupts.len());

    assert_eq!("I1", descendant_ps.interrupts[0].name);
    assert_eq!(
      "Corge",
      descendant_ps.interrupts[0].description.clone().unwrap()
    );
    assert_eq!(45, descendant_ps.interrupts[0].value);
  }

  #[test]
  fn does_not_add_inherited_interrupt() {
    let descendant_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
        <interrupt>
          <name>I1</name>
          <value>45</value>
        </interrupt>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_pi = Peripheral::parse(&descendant_el).unwrap();
    let mut descendant_ps = PeripheralSpec::new(&descendant_pi).unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO2</name>
        <baseAddress>4000</baseAddress>
        <interrupt>
          <name>I2</name>
          <description>Corge</description>
          <value>23</value>
        </interrupt>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_pi = Peripheral::parse(&ancestor_el).unwrap();
    let ancestor_ps = PeripheralSpec::new(&ancestor_pi).unwrap();

    let changed = descendant_ps.inherit_from(&ancestor_ps);

    assert!(!changed);

    assert_eq!("FOO", descendant_ps.name);
    assert_eq!(3000, descendant_ps.base_address);

    assert_eq!(1, descendant_ps.interrupts.len());

    assert_eq!("I1", descendant_ps.interrupts[0].name);
    assert!(descendant_ps.interrupts[0].description.is_none());
    assert_eq!(45, descendant_ps.interrupts[0].value);
  }

  #[test]
  fn inherits_from_returns_true_for_overridden_inherited_register() {
    let descendant_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
        <registers>
          <register>
            <name>R1</name>
            <addressOffset>100</addressOffset>
          </register>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_pi = Peripheral::parse(&descendant_el).unwrap();
    let mut descendant_ps = PeripheralSpec::new(&descendant_pi).unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO2</name>
        <baseAddress>4000</baseAddress>
        <registers>
          <register>
            <name>R1</name>
            <description>Corge</description>
            <addressOffset>200</addressOffset>
          </register>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_pi = Peripheral::parse(&ancestor_el).unwrap();
    let ancestor_ps = PeripheralSpec::new(&ancestor_pi).unwrap();

    let changed = descendant_ps.inherit_from(&ancestor_ps);

    assert!(changed);

    assert_eq!("FOO", descendant_ps.name);
    assert_eq!(3000, descendant_ps.base_address);

    assert_eq!(1, descendant_ps.registers.len());

    assert_eq!("R1", descendant_ps.registers[0].name);
    assert_eq!(
      "Corge",
      descendant_ps.registers[0].description.clone().unwrap()
    );
    assert_eq!(100, descendant_ps.registers[0].address_offset);
  }

  #[test]
  fn inherits_from_returns_true_for_added_inherited_register() {
    let descendant_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
        <registers>
          <register>
            <name>R1</name>
            <addressOffset>100</addressOffset>
          </register>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_pi = Peripheral::parse(&descendant_el).unwrap();
    let mut descendant_ps = PeripheralSpec::new(&descendant_pi).unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO2</name>
        <baseAddress>4000</baseAddress>
        <registers>
          <register>
            <name>R2</name>
            <description>Corge</description>
            <addressOffset>200</addressOffset>
          </register>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_pi = Peripheral::parse(&ancestor_el).unwrap();
    let ancestor_ps = PeripheralSpec::new(&ancestor_pi).unwrap();

    let changed = descendant_ps.inherit_from(&ancestor_ps);

    assert!(changed);

    assert_eq!("FOO", descendant_ps.name);
    assert_eq!(3000, descendant_ps.base_address);

    assert_eq!(2, descendant_ps.registers.len());

    assert_eq!("R1", descendant_ps.registers[0].name);
    assert_eq!(100, descendant_ps.registers[0].address_offset);

    assert_eq!("R2", descendant_ps.registers[1].name);
    assert_eq!(
      "Corge",
      descendant_ps.registers[1].description.clone().unwrap()
    );
    assert_eq!(200, descendant_ps.registers[1].address_offset);
  }

  #[test]
  fn inherits_from_returns_true_for_overridden_inherited_cluster() {
    let descendant_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
        <registers>
          <cluster>
            <name>C1</name>
            <addressOffset>100</addressOffset>
          </cluster>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_pi = Peripheral::parse(&descendant_el).unwrap();
    let mut descendant_ps = PeripheralSpec::new(&descendant_pi).unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO2</name>
        <baseAddress>4000</baseAddress>
        <registers>
          <cluster>
            <name>C1</name>
            <description>Corge</description>
            <addressOffset>200</addressOffset>
          </cluster>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_pi = Peripheral::parse(&ancestor_el).unwrap();
    let ancestor_ps = PeripheralSpec::new(&ancestor_pi).unwrap();

    let changed = descendant_ps.inherit_from(&ancestor_ps);

    assert!(changed);

    assert_eq!("FOO", descendant_ps.name);
    assert_eq!(3000, descendant_ps.base_address);

    assert_eq!(1, descendant_ps.clusters.len());

    assert_eq!("C1", descendant_ps.clusters[0].name);
    assert_eq!(
      "Corge",
      descendant_ps.clusters[0].description.clone().unwrap()
    );
    assert_eq!(100, descendant_ps.clusters[0].address_offset);
  }

  #[test]
  fn inherits_from_returns_true_for_added_inherited_cluster() {
    let descendant_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
        <registers>
          <cluster>
            <name>C1</name>
            <addressOffset>100</addressOffset>
          </cluster>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_pi = Peripheral::parse(&descendant_el).unwrap();
    let mut descendant_ps = PeripheralSpec::new(&descendant_pi).unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO2</name>
        <baseAddress>4000</baseAddress>
        <registers>
          <cluster>
            <name>C2</name>
            <description>Corge</description>
            <addressOffset>200</addressOffset>
          </cluster>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_pi = Peripheral::parse(&ancestor_el).unwrap();
    let ancestor_ps = PeripheralSpec::new(&ancestor_pi).unwrap();

    let changed = descendant_ps.inherit_from(&ancestor_ps);

    assert!(changed);

    assert_eq!("FOO", descendant_ps.name);
    assert_eq!(3000, descendant_ps.base_address);

    assert_eq!(2, descendant_ps.clusters.len());

    assert_eq!("C1", descendant_ps.clusters[0].name);
    assert_eq!(100, descendant_ps.clusters[0].address_offset);

    assert_eq!("C2", descendant_ps.clusters[1].name);
    assert_eq!(
      "Corge",
      descendant_ps.clusters[1].description.clone().unwrap()
    );
    assert_eq!(200, descendant_ps.clusters[1].address_offset);
  }

  #[test]
  fn has_correct_path() {
    let el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let pi = Peripheral::parse(&el).unwrap();
    let ps = PeripheralSpec::new(&pi).unwrap();

    assert_eq!("FOO", ps.path());
  }

  #[test]
  fn has_correct_derived_from_path() {
    let el: Element = Element::parse(
      r##"
      <peripheral derivedFrom="BAR">
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let pi = Peripheral::parse(&el).unwrap();
    let ps = PeripheralSpec::new(&pi).unwrap();

    assert_eq!("BAR", ps.derived_from_path().unwrap());
  }

  #[test]
  fn recursively_iterates_clusters() {
    let el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
        <registers>
          <cluster>
            <name>FOO5</name>
            <addressOffset>3000</addressOffset>
            <cluster>
              <name>FOO1</name>
              <addressOffset>3000</addressOffset>
            </cluster>
            <cluster>
              <name>FOO4</name>
              <addressOffset>3000</addressOffset>
              <cluster>
                <name>FOO2</name>
                <addressOffset>3000</addressOffset>
              </cluster>
              <cluster>
                <name>FOO3</name>
                <addressOffset>3000</addressOffset>
              </cluster>
            </cluster>
          </cluster>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let pi = Peripheral::parse(&el).unwrap();
    let ps = PeripheralSpec::new(&pi).unwrap();

    let all_clusters: Vec<&ClusterSpec> = ps.iter_clusters().collect();

    assert_eq!("FOO1", all_clusters[0].name);
    assert_eq!("FOO2", all_clusters[1].name);
    assert_eq!("FOO3", all_clusters[2].name);
    assert_eq!("FOO4", all_clusters[3].name);
    assert_eq!("FOO5", all_clusters[4].name);
  }

  #[test]
  fn recursively_mutates_clusters() {
    let el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
        <registers>
          <cluster>
            <name>FOO5</name>
            <addressOffset>3000</addressOffset>
            <cluster>
              <name>FOO1</name>
              <addressOffset>3000</addressOffset>
            </cluster>
            <cluster>
              <name>FOO4</name>
              <addressOffset>3000</addressOffset>
              <cluster>
                <name>FOO2</name>
                <addressOffset>3000</addressOffset>
              </cluster>
              <cluster>
                <name>FOO3</name>
                <addressOffset>3000</addressOffset>
              </cluster>
            </cluster>
          </cluster>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let pi = Peripheral::parse(&el).unwrap();
    let mut ps = PeripheralSpec::new(&pi).unwrap();

    let count = RefCell::new(0);

    ps.mutate_clusters(|c| {
      c.name = format!("{} {}", c.name, count.borrow());
      let current = (*count.borrow()).clone();
      *count.borrow_mut() = current + 1;
      Ok(false)
    })
    .unwrap();

    let all_clusters: Vec<&ClusterSpec> = ps.iter_clusters().collect();

    assert_eq!("FOO1 0", all_clusters[0].name);
    assert_eq!("FOO2 1", all_clusters[1].name);
    assert_eq!("FOO3 2", all_clusters[2].name);
    assert_eq!("FOO4 3", all_clusters[3].name);
    assert_eq!("FOO5 4", all_clusters[4].name);
  }

  #[test]
  fn recursively_iterates_registers() {
    let el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
        <registers>
          <cluster>
            <name>FOO5</name>
            <addressOffset>3000</addressOffset>
            <register>
              <name>FOO5</name>
              <addressOffset>3000</addressOffset>
            </register>
            <cluster>
              <name>FOO1</name>
              <addressOffset>3000</addressOffset>
              <register>
                <name>FOO1</name>
                <addressOffset>3000</addressOffset>
              </register>
            </cluster>
            <cluster>
              <name>FOO4</name>
              <addressOffset>3000</addressOffset>
              <register>
                <name>FOO4</name>
                <addressOffset>3000</addressOffset>
              </register>
              <cluster>
                <name>FOO2</name>
                <addressOffset>3000</addressOffset>
                <register>
                  <name>FOO2</name>
                  <addressOffset>3000</addressOffset>
                </register>
              </cluster>
              <cluster>
                <name>FOO3</name>
                <addressOffset>3000</addressOffset>
                <register>
                  <name>FOO3</name>
                  <addressOffset>3000</addressOffset>
                </register>
              </cluster>
            </cluster>
          </cluster>
          <register>
            <name>FOO6</name>
            <addressOffset>3000</addressOffset>
          </register>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let pi = Peripheral::parse(&el).unwrap();
    let ps = PeripheralSpec::new(&pi).unwrap();

    let all_registers: Vec<&RegisterSpec> = ps.iter_registers().collect();

    assert_eq!("FOO1", all_registers[0].name);
    assert_eq!("FOO2", all_registers[1].name);
    assert_eq!("FOO3", all_registers[2].name);
    assert_eq!("FOO4", all_registers[3].name);
    assert_eq!("FOO5", all_registers[4].name);
    assert_eq!("FOO6", all_registers[5].name);
  }

  #[test]
  fn recursively_mutates_registers() {
    let el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>3000</baseAddress>
        <registers>
          <cluster>
            <name>FOO5</name>
            <addressOffset>3000</addressOffset>
            <register>
              <name>FOO5</name>
              <addressOffset>3000</addressOffset>
            </register>
            <cluster>
              <name>FOO1</name>
              <addressOffset>3000</addressOffset>
              <register>
                <name>FOO1</name>
                <addressOffset>3000</addressOffset>
              </register>
            </cluster>
            <cluster>
              <name>FOO4</name>
              <addressOffset>3000</addressOffset>
              <register>
                <name>FOO4</name>
                <addressOffset>3000</addressOffset>
              </register>
              <cluster>
                <name>FOO2</name>
                <addressOffset>3000</addressOffset>
                <register>
                  <name>FOO2</name>
                  <addressOffset>3000</addressOffset>
                </register>
              </cluster>
              <cluster>
                <name>FOO3</name>
                <addressOffset>3000</addressOffset>
                <register>
                  <name>FOO3</name>
                  <addressOffset>3000</addressOffset>
                </register>
              </cluster>
            </cluster>
          </cluster>
          <register>
            <name>FOO6</name>
            <addressOffset>3000</addressOffset>
          </register>
        </registers>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let pi = Peripheral::parse(&el).unwrap();
    let mut ps = PeripheralSpec::new(&pi).unwrap();

    let count = RefCell::new(0);

    ps.mutate_registers(|r| {
      r.name = format!("{} {}", r.name, count.borrow());
      let current = (*count.borrow()).clone();
      *count.borrow_mut() = current + 1;
      Ok(false)
    })
    .unwrap();

    let all_registers: Vec<&RegisterSpec> = ps.iter_registers().collect();

    assert_eq!("FOO1 0", all_registers[0].name);
    assert_eq!("FOO2 1", all_registers[1].name);
    assert_eq!("FOO3 2", all_registers[2].name);
    assert_eq!("FOO4 3", all_registers[3].name);
    assert_eq!("FOO5 4", all_registers[4].name);
    assert_eq!("FOO6 5", all_registers[5].name);
  }

  #[test]
  pub fn propagates_default_register_properties() {
    let el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>5000</baseAddress>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let pi = Peripheral::parse(&el).unwrap();
    let mut peripheral = PeripheralSpec::new(&pi).unwrap();

    let changed = peripheral.propagate_default_register_properties(
      Some(1),
      Some(2),
      Some(3),
      Some(AccessSpec::ReadWriteOnce),
    );

    assert!(changed);
    assert_eq!(1, peripheral.default_register_size.unwrap());
    assert_eq!(2, peripheral.default_register_reset_value.unwrap());
    assert_eq!(3, peripheral.default_register_reset_mask.unwrap());
    assert_eq!(
      AccessSpec::ReadWriteOnce,
      peripheral.default_register_access.unwrap()
    );
  }

  #[test]
  pub fn propagate_default_register_properties_returns_false_when_no_changes() {
    let el: Element = Element::parse(
      r##"
      <peripheral>
        <name>FOO</name>
        <baseAddress>5000</baseAddress>
      </peripheral>
      "##
        .as_bytes(),
    )
    .unwrap();

    let pi = Peripheral::parse(&el).unwrap();
    let mut peripheral = PeripheralSpec::new(&pi).unwrap();

    let changed = peripheral.propagate_default_register_properties(None, None, None, None);

    assert!(!changed);
    assert!(peripheral.default_register_access.is_none());
    assert!(peripheral.default_register_reset_value.is_none());
    assert!(peripheral.default_register_reset_mask.is_none());
    assert!(peripheral.default_register_size.is_none());
  }
}
