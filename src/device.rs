use super::{peripheral::PeripheralSpec, AccessSpec, ClusterSpec, FieldSpec, RegisterSpec};
use crate::{
  error::{SvdExpanderError, SvdExpanderResult},
  value::EnumeratedValueSetSpec,
};
use svd_parser::{Cpu, Device, Endian};

/// Defines the endianness of a CPU.
///
/// # Values
///
/// * `Little` = Little-endian memory (least-significant bit gets allocated at the lowest address).
/// * `Big` = Big-endian memory (most-significant bit gets allocated at the lowest address).
/// * `Selectable` = Endianness is configurable and becomes active after the next reset.
/// * `Other` = The endianness is neither big nor little endian.
#[derive(Debug, Clone, PartialEq)]
pub enum EndianSpec {
  /// Little-endian memory (least-significant bit gets allocated at the lowest address).
  Little,

  /// Big-endian memory (most-significant bit gets allocated at the lowest address).
  Big,

  /// Endianness is configurable and becomes active after the next reset.
  Selectable,

  /// The endianness is neither big nor little endian.
  Other,
}
impl EndianSpec {
  pub(crate) fn new(e: &Endian) -> Self {
    match e {
      Endian::Little => EndianSpec::Little,
      Endian::Big => EndianSpec::Big,
      Endian::Selectable => EndianSpec::Selectable,
      Endian::Other => EndianSpec::Other,
    }
  }
}

/// Describes the processor included in the microcontroller device.
#[derive(Debug, Clone, PartialEq)]
pub struct CpuSpec {
  /// The unique name of the device's CPU.
  pub name: String,

  /// The hardware revision of the processor. The format is rNpM (N,M = [0 - 99]).
  pub revision: String,

  /// The endianness of the processor.
  pub endian: EndianSpec,

  /// Whether the processor is equipped with a memory protection unit.
  pub mpu_present: bool,

  /// Whether the processor is equipped with a hardware floating point unit.
  pub fpu_present: bool,

  /// The number of bits available in the Nested Vector Interrupt Controller (NVIC) for
  /// configuring priority.
  pub nvic_priority_bits: u32,

  /// Whether the processor implements a vendor-specific System Tick Timer.
  pub has_vendor_systick: bool,
}
impl CpuSpec {
  pub(crate) fn new(c: &Cpu) -> Self {
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

/// Represents information about a device specified in a CMSIS-SVD file.
#[derive(Debug, Clone, PartialEq)]
pub struct DeviceSpec {
  // Uniquely identifies the device.
  pub name: String,

  /// The full name of the vendor of the device.
  pub version: Option<String>,

  /// Description of the main features of the device (i.e. CPU, clock frequency, peripheral
  /// overview).
  pub description: Option<String>,

  /// The number of data bits uniquely selected by each address. The value for Cortex-M-based
  /// devices is `8` (byte-addressable).
  pub address_unit_bits: Option<u32>,

  /// The bit width of the maximum single data transfer supported by bu bus infrastructure.
  /// Expected value for Cortex-M-based devices is 32.
  pub width: Option<u32>,

  /// The processor included in the device.
  pub cpu: Option<CpuSpec>,

  /// The device's peripherals.
  pub peripherals: Vec<PeripheralSpec>,

  /// Default bit width of any register contained in the device.
  pub default_register_size: Option<u32>,

  /// Default value of all registers after reset.
  pub default_register_reset_value: Option<u32>,

  /// Defines which register bits have a defined reset value.
  pub default_register_reset_mask: Option<u32>,

  /// Default access rights for all registers.
  pub default_register_access: Option<AccessSpec>,
}
impl DeviceSpec {
  /// Creates a new device by parsing an XML string following the CMSIS-SVD specification.
  /// Expands all array definitions and resolves inheritance chains to fully resolve all
  /// populate all the components of the device.
  ///
  /// # Arguments
  ///
  /// * `xml` = An XML string containing a device specification in the CMSIS-SVD format.
  ///
  /// # Example
  ///
  /// ```
  /// use svd_expander::DeviceSpec;
  /// let device = DeviceSpec::from_xml(
  ///   r##"
  ///   <device
  ///     xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" schemaVersion="1.1" xsi:noNamespaceSchemaLocation="CMSIS-SVD_Schema_1_1.xsd">
  ///     <name>STM32F303</name>
  ///     <version>1.2</version>
  ///     <peripherals>
  ///     </peripherals>
  ///   </device>
  ///   "##
  /// ).unwrap();
  ///
  /// assert_eq!("STM32F303", device.name);
  /// assert_eq!("1.2", device.version.unwrap());
  /// ```
  pub fn from_xml(xml: &str) -> SvdExpanderResult<Self> {
    Ok(Self::new(&svd_parser::parse(xml)?)?)
  }

  pub(crate) fn new(d: &Device) -> SvdExpanderResult<Self> {
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
        .collect::<SvdExpanderResult<Vec<PeripheralSpec>>>()?,
      default_register_reset_value: d.default_register_properties.reset_value,
      default_register_reset_mask: d.default_register_properties.reset_mask,
      default_register_size: d.default_register_properties.size,
      default_register_access: match d.default_register_properties.access {
        Some(ref a) => Some(AccessSpec::new(a)),
        None => None,
      },
    };

    // Resolve any inheritance chains. Each repetition resolves one level of
    // inheritance. We continue until the method returns false, which means
    // there were no changes and all the chains are fully resolved.
    while device.expand_inherited()? {}

    // Propagate default register properties down to the registers.
    while device.propagate_default_register_properties() {}

    // Propagate register access values down to their fields, if the
    // fields have not specified their own.
    device.propagate_field_access()?;

    Ok(device)
  }

  /// Recursively iterates all the register clusters on the device.
  pub fn iter_clusters(&self) -> impl Iterator<Item = &ClusterSpec> {
    self.peripherals.iter().flat_map(|p| p.iter_clusters())
  }

  /// Recursively iterates all the registers on the device.
  pub fn iter_registers(&self) -> impl Iterator<Item = &RegisterSpec> {
    self.peripherals.iter().flat_map(|p| p.iter_registers())
  }

  /// Recursively iterates all the register fields on the device.
  pub fn iter_fields(&self) -> impl Iterator<Item = &FieldSpec> {
    self.peripherals.iter().flat_map(|p| p.iter_fields())
  }

  /// Recursively iterates all the enumerated value sets on the device.
  pub fn iter_enumerated_value_sets(&self) -> impl Iterator<Item = &EnumeratedValueSetSpec> {
    self
      .peripherals
      .iter()
      .flat_map(|p| p.iter_enumerated_value_sets())
  }

  /// Gets the peripheral that exists at the given path. Peripherals
  /// top-level constructs and can't be nested, so a peripheral path
  /// is simply the name of the peripheral.
  ///
  /// # Arguments
  ///
  /// * `path` = The path to the peripheral. Since peripherals are top-level
  /// components and can't be nested, this is just the name of the peripheral.
  pub fn get_peripheral(&self, path: &str) -> SvdExpanderResult<&PeripheralSpec> {
    match self.peripherals.iter().find(|p| p.path() == path) {
      Some(p) => Ok(p),
      None => Err(SvdExpanderError::new(&format!(
        "No peripheral at path '{}'",
        path
      ))),
    }
  }

  /// Gets the register cluster that exists at the given path.
  ///
  /// # Arguments
  ///
  /// * `path` = The path to the register cluster.
  pub fn get_cluster(&self, path: &str) -> SvdExpanderResult<&ClusterSpec> {
    match self.iter_clusters().find(|c| c.path() == path) {
      Some(c) => Ok(c),
      None => Err(SvdExpanderError::new(&format!(
        "No cluster at path '{}'",
        path
      ))),
    }
  }

  /// Gets the register that exists at the given path.
  ///
  /// # Arguments
  ///
  /// * `path` = The path to the register.
  pub fn get_register(&self, path: &str) -> SvdExpanderResult<&RegisterSpec> {
    match self.iter_registers().find(|r| r.path() == path) {
      Some(r) => Ok(r),
      None => Err(SvdExpanderError::new(&format!(
        "No register at path '{}'",
        path
      ))),
    }
  }

  /// Gets the register field that exists at the given path.
  ///
  /// # Arguments
  ///
  /// * `path` = The path to the register field.
  pub fn get_field(&self, path: &str) -> SvdExpanderResult<&FieldSpec> {
    match self.iter_fields().find(|f| f.path() == path) {
      Some(r) => Ok(r),
      None => Err(SvdExpanderError::new(&format!(
        "No field at path '{}'",
        path
      ))),
    }
  }

  /// Gets the enumerated value set that exists at the given path.
  ///
  /// # Arguments
  ///
  /// * `path` = The path to the enumerated value set.
  pub (crate) fn get_enumerated_value_set(&self, path: &str) -> SvdExpanderResult<&EnumeratedValueSetSpec> {
    let set = self.iter_enumerated_value_sets().find(|s| match s.path() {
      Some(ref p) => p == path,
      None => false,
    });

    match set {
      Some(ref s) => Ok(s),
      None => Err(SvdExpanderError::new(&format!(
        "No enumerated value set at path '{}'",
        path
      ))),
    }
  }

  fn expand_inherited(&mut self) -> SvdExpanderResult<bool> {
    let reference_device = self.clone();

    let mut changed = false;

    for peripheral in self.peripherals.iter_mut() {
      if peripheral.mutate_enumerated_value_sets(|s| {
        let mut set_changed = false;

        if let Some(ref derived_from) = s.derived_from_path()? {
          if s.inherit_from(reference_device.get_enumerated_value_set(derived_from)?) {
            set_changed = true;
          }
        }

        Ok(set_changed)
      })? {
        changed = true;
      }
    }

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
        &self.default_register_size,
        &self.default_register_reset_value,
        &self.default_register_reset_mask,
        &self.default_register_access,
      ) {
        changed = true;
      }
    }

    return changed;
  }

  fn propagate_field_access(&mut self) -> SvdExpanderResult<()> {
    for peripheral in self.peripherals.iter_mut() {
      peripheral.mutate_registers(|r| {
        if let Some(ref access) = r.access {
          for field in r.fields.iter_mut() {
            if field.access.is_none() {
              field.access = Some(access.clone());
            }
          }
        }
        // Whether we return true or false is irrelevant. We're not propagating
        // changes through multiple levels of the tree so it doesn't matter whether
        // anything changed or not.
        Ok(true)
      })?;
    }

    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::{DeviceSpec, EndianSpec};
  use crate::{
    value::{
      EnumeratedValueValueSpec, ModifiedWriteValuesSpec, WriteConstraintRangeSpec,
      WriteConstraintSpec,
    },
    AccessSpec,
  };
  use svd_parser::{parse::Parse, Device};
  use xmltree::Element;

  #[test]
  fn can_create_from_xml() {
    let el: Element = Element::parse(
      r##"
      <device
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

  #[test]
  fn resolves_everything() {
    let ds = DeviceSpec::from_xml(
      r##"
      <?xml version="1.0" encoding="utf-8"?>

      <!-- File naming: <part/series name>.svd -->

      <!--
        Copyright (C) 2012-2014 ARM Limited. All rights reserved.

        Purpose: System Viewer Description (SVD) Example (Schema Version 1.1)
                This is a description of a none-existent and incomplete device
            for demonstration purposes only.
            
        Redistribution and use in source and binary forms, with or without
        modification, are permitted provided that the following conditions are met:
        - Redistributions of source code must retain the above copyright
          notice, this list of conditions and the following disclaimer.
        - Redistributions in binary form must reproduce the above copyright
          notice, this list of conditions and the following disclaimer in the
          documentation and/or other materials provided with the distribution.
        - Neither the name of ARM nor the names of its contributors may be used 
          to endorse or promote products derived from this software without 
          specific prior written permission.

        THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" 
        AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE 
        IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
        ARE DISCLAIMED. IN NO EVENT SHALL COPYRIGHT HOLDERS AND CONTRIBUTORS BE
        LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
        CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF 
        SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS 
        INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN 
        CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) 
        ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
        POSSIBILITY OF SUCH DAMAGE.
      -->
      
      <device schemaVersion="1.1" xmlns:xs="http://www.w3.org/2001/XMLSchema-instance" xs:noNamespaceSchemaLocation="CMSIS-SVD.xsd" >
        <vendor>ARM Ltd.</vendor>                                       <!-- device vendor name -->
        <vendorID>ARM</vendorID>                                        <!-- device vendor short name -->
        <name>ARM_Example</name>                                        <!-- name of part-->
        <series>ARMCM3</series>                                         <!-- device series the device belongs to -->
        <version>1.2</version>                                          <!-- version of this description, adding CMSIS-SVD 1.1 tags -->
        <description>ARM 32-bit Cortex-M3 Microcontroller based device, CPU clock up to 80MHz, etc. </description>
        <licenseText>                                                   <!-- this license text will appear in header file. \n force line breaks -->
          ARM Limited (ARM) is supplying this software for use with Cortex-M\n
          processor based microcontroller, but can be equally used for other\n
          suitable  processor architectures. This file can be freely distributed.\n
          Modifications to this file shall be clearly marked.\n
          \n
          THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED\n
          OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF\n
          MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.\n
          ARM SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR\n
          CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
        </licenseText>
        <cpu>                                                           <!-- details about the cpu embedded in the device -->
          <name>CM3</name>
          <revision>r1p0</revision>
          <endian>little</endian>
          <mpuPresent>true</mpuPresent>
          <fpuPresent>false</fpuPresent>
          <nvicPrioBits>3</nvicPrioBits>
          <vendorSystickConfig>false</vendorSystickConfig>
        </cpu>
        <addressUnitBits>8</addressUnitBits>                            <!-- byte addressable memory -->
        <width>32</width>                                               <!-- bus width is 32 bits -->
        <!-- default settings implicitly inherited by subsequent sections -->
        <size>32</size>                                                 <!-- this is the default size (number of bits) of all peripherals
                                                                            and register that do not define "size" themselves -->
        <access>read-write</access>                                     <!-- default access permission for all subsequent registers -->
        <resetValue>0x00000000</resetValue>                             <!-- by default all bits of the registers are initialized to 0 on reset -->
        <resetMask>0xFFFFFFFF</resetMask>                               <!-- by default all 32Bits of the registers are used -->

        <peripherals>
          <!-- Timer 0 -->
          <peripheral>
            <name>TIMER0</name>
            <version>1.0</version>
            <description>32 Timer / Counter, counting up or down from different sources</description>
            <groupName>TIMER</groupName>
            <baseAddress>0x40010000</baseAddress>
            <size>32</size>
            <access>read-write</access>

            <addressBlock>
              <offset>0</offset>
              <size>0x100</size>
              <usage>registers</usage>
            </addressBlock>

            <interrupt>
              <name>TIMER0</name>
              <description>Timer 0 interrupt</description>
              <value>0</value>
            </interrupt>

            <registers>
            <!-- CR: Control Register -->
              <register>
                <name>CR</name>
                <description>Control Register</description>
                <addressOffset>0x00</addressOffset>
                <size>32</size>
                <access>read-write</access>
                <resetValue>0x00000000</resetValue>
                <resetMask>0x1337F7F</resetMask>

                <fields>
                  <!-- EN: Enable -->
                  <field>
                    <name>EN</name>
                    <description>Enable</description>
                    <bitRange>[0:0]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>Disable</name>
                        <description>Timer is disabled and does not operate</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Enable</name>
                        <description>Timer is enabled and can operate</description>
                        <value>1</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- RST: Reset -->
                  <field>
                    <name>RST</name>
                    <description>Reset Timer</description>
                    <bitRange>[1:1]</bitRange>
                    <access>write-only</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>No_Action</name>
                        <description>Write as ZERO if necessary</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Reset_Timer</name>
                        <description>Reset the Timer</description>
                        <value>1</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- CNT: Counting Direction -->
                  <field>
                    <name>CNT</name>
                    <description>Counting direction</description>
                    <bitRange>[3:2]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>Count_UP</name>
                        <description>Timer Counts UO and wraps, if no STOP condition is set</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Count_DOWN</name>
                        <description>Timer Counts DOWN and wraps, if no STOP condition is set</description>
                        <value>1</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Toggle</name>
                        <description>Timer Counts up to MAX, then DOWN to ZERO, if no STOP condition is set</description>
                        <value>2</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- MODE: Operation Mode -->
                  <field>
                    <name>MODE</name>
                    <description>Operation Mode</description>
                    <bitRange>[6:4]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>Continous</name>
                        <description>Timer runs continously</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Single_ZERO_MAX</name>
                        <description>Timer counts to 0x00 or 0xFFFFFFFF (depending on CNT) and stops</description>
                        <value>1</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Single_MATCH</name>
                        <description>Timer counts to the Value of MATCH Register and stops</description>
                        <value>2</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Reload_ZERO_MAX</name>
                        <description>Timer counts to 0x00 or 0xFFFFFFFF (depending on CNT), loads the RELOAD Value and continues</description>
                        <value>3</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Reload_MATCH</name>
                        <description>Timer counts to the Value of MATCH Register, loads the RELOAD Value and continues</description>
                        <value>4</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- PSC: Use Prescaler -->
                  <field>
                    <name>PSC</name>
                    <description>Use Prescaler</description>
                    <bitRange>[7:7]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>Disabled</name>
                        <description>Prescaler is not used</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Enabled</name>
                        <description>Prescaler is used as divider</description>
                        <value>1</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- CNTSRC: Timer / Counter Soruce Divider -->
                  <field>
                    <name>CNTSRC</name>
                    <description>Timer / Counter Source Divider</description>
                    <bitRange>[11:8]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>CAP_SRC</name>
                        <description>Capture Source is used directly</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>CAP_SRC_div2</name>
                        <description>Capture Source is divided by 2</description>
                        <value>1</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>CAP_SRC_div4</name>
                        <description>Capture Source is divided by 4</description>
                        <value>2</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>CAP_SRC_div8</name>
                        <description>Capture Source is divided by 8</description>
                        <value>3</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>CAP_SRC_div16</name>
                        <description>Capture Source is divided by 16</description>
                        <value>4</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>CAP_SRC_div32</name>
                        <description>Capture Source is divided by 32</description>
                        <value>5</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>CAP_SRC_div64</name>
                        <description>Capture Source is divided by 64</description>
                        <value>6</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>CAP_SRC_div128</name>
                        <description>Capture Source is divided by 128</description>
                        <value>7</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>CAP_SRC_div256</name>
                        <description>Capture Source is divided by 256</description>
                        <value>8</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- CAPSRC: Timer / COunter Capture Source -->
                  <field>
                    <name>CAPSRC</name>
                    <description>Timer / Counter Capture Source</description>
                    <bitRange>[15:12]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>CClk</name>
                        <description>Core Clock</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOA_0</name>
                        <description>GPIO A, PIN 0</description>
                        <value>1</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOA_1</name>
                        <description>GPIO A, PIN 1</description>
                        <value>2</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOA_2</name>
                        <description>GPIO A, PIN 2</description>
                        <value>3</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOA_3</name>
                        <description>GPIO A, PIN 3</description>
                        <value>4</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOA_4</name>
                        <description>GPIO A, PIN 4</description>
                        <value>5</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOA_5</name>
                        <description>GPIO A, PIN 5</description>
                        <value>6</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOA_6</name>
                        <description>GPIO A, PIN 6</description>
                        <value>7</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOA_7</name>
                        <description>GPIO A, PIN 7</description>
                        <value>8</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOB_0</name>
                        <description>GPIO B, PIN 0</description>
                        <value>9</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOB_1</name>
                        <description>GPIO B, PIN 1</description>
                        <value>10</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOB_2</name>
                        <description>GPIO B, PIN 2</description>
                        <value>11</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOB_3</name>
                        <description>GPIO B, PIN 3</description>
                        <value>12</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOC_0</name>
                        <description>GPIO C, PIN 0</description>
                        <value>13</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOC_5</name>
                        <description>GPIO C, PIN 1</description>
                        <value>14</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>GPIOC_6</name>
                        <description>GPIO C, PIN 2</description>
                        <value>15</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- CAPEDGE: Capture Edge -->
                  <field>
                    <name>CAPEDGE</name>
                    <description>Capture Edge, select which Edge should result in a counter increment or decrement</description>
                    <bitRange>[17:16]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>RISING</name>
                        <description>Only rising edges result in a counter increment or decrement</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>FALLING</name>
                        <description>Only falling edges  result in a counter increment or decrement</description>
                        <value>1</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>BOTH</name>
                        <description>Rising and falling edges result in a counter increment or decrement</description>
                        <value>2</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- TRGEXT: Triggers an other Peripheral -->
                  <field>
                    <name>TRGEXT</name>
                    <description>Triggers an other Peripheral</description>
                    <bitRange>[21:20]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>NONE</name>
                        <description>No Trigger is emitted</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>DMA1</name>
                        <description>DMA Controller 1 is triggered, dependant on MODE</description>
                        <value>1</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>DMA2</name>
                        <description>DMA Controller 2 is triggered, dependant on MODE</description>
                        <value>2</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>UART</name>
                        <description>UART is triggered, dependant on MODE</description>
                        <value>3</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- Reload: Selects Reload Register n -->
                  <field>
                    <name>RELOAD</name>
                    <description>Select RELOAD Register n to reload Timer on condition</description>
                    <bitRange>[25:24]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>RELOAD0</name>
                        <description>Selects Reload Register number 0</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>RELOAD1</name>
                        <description>Selects Reload Register number 1</description>
                        <value>1</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>RELOAD2</name>
                        <description>Selects Reload Register number 2</description>
                        <value>2</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>RELOAD3</name>
                        <description>Selects Reload Register number 3</description>
                        <value>3</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- IDR: Inc or dec Reload Register Selection -->
                  <field>
                    <name>IDR</name>
                    <description>Selects, if Reload Register number is incremented, decremented or not modified</description>
                    <bitRange>[27:26]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>KEEP</name>
                        <description>Reload Register number does not change automatically</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>INCREMENT</name>
                        <description>Reload Register number is incremented on each match</description>
                        <value>1</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>DECREMENT</name>
                        <description>Reload Register number is decremented on each match</description>
                        <value>2</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- START: Starts / Stops the Timer/Counter -->
                  <field>
                    <name>S</name>
                    <description>Starts and Stops the Timer / Counter</description>
                    <bitRange>[31:31]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>STOP</name>
                        <description>Timer / Counter is stopped</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>START</name>
                        <description>Timer / Counter is started</description>
                        <value>1</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>
                </fields>
              </register>

              <!-- SR: Status Register -->
              <register>
                <name>SR</name>
                <description>Status Register</description>
                <addressOffset>0x04</addressOffset>
                <size>16</size>
                <access>read-write</access>
                <resetValue>0x00000000</resetValue>
                <resetMask>0xD701</resetMask>

                <fields>
                  <!-- RUN: Shows if Timer is running -->
                  <field>
                    <name>RUN</name>
                    <description>Shows if Timer is running or not</description>
                    <bitRange>[0:0]</bitRange>
                    <access>read-only</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>Stopped</name>
                        <description>Timer is not running</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Running</name>
                        <description>Timer is running</description>
                        <value>1</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- MATCH: Shows if a Match was hit -->
                  <field>
                    <name>MATCH</name>
                    <description>Shows if the MATCH was hit</description>
                    <bitRange>[8:8]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>No_Match</name>
                        <description>The MATCH condition was not hit</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Match_Hit</name>
                        <description>The MATCH condition was hit</description>
                        <value>1</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- UN: Shows if an underflow occured -->
                  <field>
                    <name>UN</name>
                    <description>Shows if an underflow occured. This flag is sticky</description>
                    <bitRange>[9:9]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>No_Underflow</name>
                        <description>No underflow occured since last clear</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Underflow</name>
                        <description>A minimum of one underflow occured since last clear</description>
                        <value>1</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- OV: Shows if an overflow occured -->
                  <field>
                    <name>OV</name>
                    <description>Shows if an overflow occured. This flag is sticky</description>
                    <bitRange>[10:10]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>No_Overflow</name>
                        <description>No overflow occured since last clear</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Overflow_occured</name>
                        <description>A minimum of one overflow occured since last clear</description>
                        <value>1</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- RST: Shows if Timer is in RESET state -->
                  <field>
                    <name>RST</name>
                    <description>Shows if Timer is in RESET state</description>
                    <bitRange>[12:12]</bitRange>
                    <access>read-only</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>Ready</name>
                        <description>Timer is not in RESET state and can operate</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>In_Reset</name>
                        <description>Timer is in RESET state and can not operate</description>
                        <value>1</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- RELOAD: Shows the currently active Reload Register -->
                  <field>
                    <name>RELOAD</name>
                    <description>Shows the currently active RELOAD Register</description>
                    <bitRange>[15:14]</bitRange>
                    <access>read-only</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>RELOAD0</name>
                        <description>Reload Register number 0 is active</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>RELOAD1</name>
                        <description>Reload Register number 1 is active</description>
                        <value>1</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>RELOAD2</name>
                        <description>Reload Register number 2 is active</description>
                        <value>2</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>RELOAD3</name>
                        <description>Reload Register number 3 is active</description>
                        <value>3</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>
                </fields>
              </register>

              <!-- INT: Interrupt Register -->
              <register>
                <name>INT</name>
                <description>Interrupt Register</description>
                <addressOffset>0x10</addressOffset>
                <size>16</size>
                <access>read-write</access>
                <resetValue>0x00000000</resetValue>
                <resetMask>0x0771</resetMask>
                <writeConstraint>
                  <range>
                    <minimum>2</minimum>
                    <maximum>4</maximum>
                  </range>
                </writeConstraint>
                <modifiedWriteValues>oneToToggle</modifiedWriteValues>

                <fields>
                  <!-- EN: Interrupt Enable -->
                  <field>
                    <name>EN</name>
                    <description>Interrupt Enable</description>
                    <bitRange>[0:0]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>Disabled</name>
                        <description>Timer does not generate Interrupts</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Enable</name>
                        <description>Timer triggers the TIMERn Interrupt</description>
                        <value>1</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>

                  <!-- MODE: Interrupt Mode -->
                  <field>
                    <name>MODE</name>
                    <description>Interrupt Mode, selects on which condition the Timer should generate an Interrupt</description>
                    <bitRange>[6:4]</bitRange>
                    <access>read-write</access>
                    <enumeratedValues>
                      <enumeratedValue>
                        <name>Match</name>
                        <description>Timer generates an Interrupt when the MATCH condition is hit</description>
                        <value>0</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Underflow</name>
                        <description>Timer generates an Interrupt when it underflows</description>
                        <value>1</value>
                      </enumeratedValue>
                      <enumeratedValue>
                        <name>Overflow</name>
                        <description>Timer generates an Interrupt when it overflows</description>
                        <value>2</value>
                      </enumeratedValue>
                    </enumeratedValues>
                  </field>
                </fields>
              </register>

              <!-- COUNT: Counter Register -->
              <register>
                <name>COUNT</name>
                <description>The Counter Register reflects the actual Value of the Timer/Counter</description>
                <addressOffset>0x20</addressOffset>
                <size>32</size>
                <access>read-write</access>
                <resetValue>0x00000000</resetValue>
                <resetMask>0xFFFFFFFF</resetMask>
              </register>

              <!-- MATCH: Match Register -->
              <register>
                <name>MATCH</name>
                <description>The Match Register stores the compare Value for the MATCH condition</description>
                <addressOffset>0x24</addressOffset>
                <size>32</size>
                <access>read-write</access>
                <resetValue>0x00000000</resetValue>
                <resetMask>0xFFFFFFFF</resetMask>
              </register>
              
              <!-- PRESCALE: Prescale Read Register -->
              <register>
                <name>PRESCALE_RD</name>
                <description>The Prescale Register stores the Value for the prescaler. The cont event gets divided by this value</description>
                <addressOffset>0x28</addressOffset>
                <size>32</size>
                <access>read-only</access>
                <resetValue>0x00000000</resetValue>
                <resetMask>0xFFFFFFFF</resetMask>
              </register>
              
              <!-- PRESCALE: Prescale Write Register -->
              <register>
                <name>PRESCALE_WR</name>
                <description>The Prescale Register stores the Value for the prescaler. The cont event gets divided by this value</description>
                <addressOffset>0x28</addressOffset>
                <size>32</size>
                <access>write-only</access>
                <resetValue>0x00000000</resetValue>
                <resetMask>0xFFFFFFFF</resetMask>
              </register>


              <!-- RELOAD: Array of Reload Register with 4 elements-->
              <register>
                <dim>4</dim>
                <dimIncrement>4</dimIncrement>
                <name>RELOAD[%s]</name>
                <description>The Reload Register stores the Value the COUNT Register gets reloaded on a when a condition was met.</description>
                <addressOffset>0x50</addressOffset>
                <size>32</size>
                <access>read-write</access>
                <resetValue>0x00000000</resetValue>
                <resetMask>0xFFFFFFFF</resetMask>
              </register>
            </registers>
          </peripheral>

          <!-- Timer 1 -->
          <peripheral derivedFrom="TIMER0">
            <name>TIMER1</name>
            <baseAddress>0x40010100</baseAddress>
            <interrupt>
              <name>TIMER1</name>
              <description>Timer 2 interrupt</description>
              <value>4</value>
            </interrupt>
          </peripheral>

          <!-- Timer 2 -->
          <peripheral derivedFrom="TIMER1">
            <name>TIMER2</name>
            <baseAddress>0x40010200</baseAddress>
            <interrupt>
              <name>TIMER2</name>
              <description>Timer 2 interrupt</description>
              <value>6</value>
            </interrupt>
          </peripheral>
        </peripherals>
      </device>
      "##
    ).unwrap();

    let timer0 = ds.get_peripheral("TIMER0").unwrap();
    assert_eq!("TIMER0", timer0.name);
    assert_eq!(1, timer0.interrupts.len());
    assert_eq!(0x40010000, timer0.base_address);
    assert_eq!(
      "32 Timer / Counter, counting up or down from different sources",
      timer0.description.clone().unwrap()
    );
    assert_eq!(11, timer0.registers.len());
    assert_eq!("RELOAD[0]", timer0.registers[7].name);
    assert_eq!("RELOAD[1]", timer0.registers[8].name);
    assert_eq!("RELOAD[2]", timer0.registers[9].name);
    assert_eq!("RELOAD[3]", timer0.registers[10].name);

    let timer1 = ds.get_peripheral("TIMER1").unwrap();
    assert_eq!("TIMER1", timer1.name);
    assert_eq!(1, timer1.interrupts.len());
    assert_eq!(0x40010100, timer1.base_address);
    assert_eq!(
      "32 Timer / Counter, counting up or down from different sources",
      timer1.description.clone().unwrap()
    );
    assert_eq!(11, timer1.registers.len());
    assert_eq!("RELOAD[0]", timer1.registers[7].name);
    assert_eq!("RELOAD[1]", timer1.registers[8].name);
    assert_eq!("RELOAD[2]", timer1.registers[9].name);
    assert_eq!("RELOAD[3]", timer1.registers[10].name);

    let timer2 = ds.get_peripheral("TIMER2").unwrap();
    assert_eq!("TIMER2", timer2.name);
    assert_eq!(1, timer2.interrupts.len());
    assert_eq!(0x40010200, timer2.base_address);
    assert_eq!(
      "32 Timer / Counter, counting up or down from different sources",
      timer2.description.clone().unwrap()
    );
    assert_eq!(11, timer2.registers.len());
    assert_eq!("RELOAD[0]", timer2.registers[7].name);
    assert_eq!("RELOAD[1]", timer2.registers[8].name);
    assert_eq!("RELOAD[2]", timer2.registers[9].name);
    assert_eq!("RELOAD[3]", timer2.registers[10].name);

    let timer0_interrupt_mode = ds.get_field("TIMER0.INT.MODE").unwrap();
    assert_eq!("MODE", timer0_interrupt_mode.name);
    assert!(timer0_interrupt_mode.derived_from_path().is_none());
    assert_eq!(
      WriteConstraintSpec::Range(WriteConstraintRangeSpec { min: 2, max: 4 }),
      timer0_interrupt_mode.write_constraint.clone().unwrap()
    );
    assert_eq!(
      ModifiedWriteValuesSpec::OneToToggle,
      timer0_interrupt_mode.modified_write_values.clone().unwrap()
    );
    assert_eq!(1, timer0_interrupt_mode.enumerated_value_sets.len());
    assert_eq!(
      3,
      timer0_interrupt_mode.enumerated_value_sets[0].values.len()
    );
    assert_eq!(
      "Match",
      timer0_interrupt_mode.enumerated_value_sets[0].values[0].name
    );
    assert_eq!(
      Some(EnumeratedValueValueSpec::Value(0)),
      timer0_interrupt_mode.enumerated_value_sets[0].values[0].value
    );
    assert_eq!(
      "Underflow",
      timer0_interrupt_mode.enumerated_value_sets[0].values[1].name
    );
    assert_eq!(
      Some(EnumeratedValueValueSpec::Value(1)),
      timer0_interrupt_mode.enumerated_value_sets[0].values[1].value
    );
    assert_eq!(
      "Overflow",
      timer0_interrupt_mode.enumerated_value_sets[0].values[2].name
    );
    assert_eq!(
      Some(EnumeratedValueValueSpec::Value(2)),
      timer0_interrupt_mode.enumerated_value_sets[0].values[2].value
    );

    let timer1_interrupt_mode = ds.get_field("TIMER1.INT.MODE").unwrap();
    assert_eq!("MODE", timer1_interrupt_mode.name);
    assert!(timer1_interrupt_mode.derived_from_path().is_none());
    assert_eq!(
      WriteConstraintSpec::Range(WriteConstraintRangeSpec { min: 2, max: 4 }),
      timer1_interrupt_mode.write_constraint.clone().unwrap()
    );
    assert_eq!(
      ModifiedWriteValuesSpec::OneToToggle,
      timer1_interrupt_mode.modified_write_values.clone().unwrap()
    );
    assert_eq!(1, timer1_interrupt_mode.enumerated_value_sets.len());
    assert_eq!(
      3,
      timer1_interrupt_mode.enumerated_value_sets[0].values.len()
    );
    assert_eq!(
      "Match",
      timer1_interrupt_mode.enumerated_value_sets[0].values[0].name
    );
    assert_eq!(
      Some(EnumeratedValueValueSpec::Value(0)),
      timer1_interrupt_mode.enumerated_value_sets[0].values[0].value
    );
    assert_eq!(
      "Underflow",
      timer1_interrupt_mode.enumerated_value_sets[0].values[1].name
    );
    assert_eq!(
      Some(EnumeratedValueValueSpec::Value(1)),
      timer1_interrupt_mode.enumerated_value_sets[0].values[1].value
    );
    assert_eq!(
      "Overflow",
      timer1_interrupt_mode.enumerated_value_sets[0].values[2].name
    );
    assert_eq!(
      Some(EnumeratedValueValueSpec::Value(2)),
      timer1_interrupt_mode.enumerated_value_sets[0].values[2].value
    );

    let timer2_interrupt_mode = ds.get_field("TIMER2.INT.MODE").unwrap();
    assert_eq!("MODE", timer2_interrupt_mode.name);
    assert!(timer2_interrupt_mode.derived_from_path().is_none());
    assert_eq!(
      WriteConstraintSpec::Range(WriteConstraintRangeSpec { min: 2, max: 4 }),
      timer2_interrupt_mode.write_constraint.clone().unwrap()
    );
    assert_eq!(
      ModifiedWriteValuesSpec::OneToToggle,
      timer2_interrupt_mode.modified_write_values.clone().unwrap()
    );
    assert_eq!(
      WriteConstraintSpec::Range(WriteConstraintRangeSpec { min: 2, max: 4 }),
      timer2_interrupt_mode.write_constraint.clone().unwrap()
    );
    assert_eq!(
      ModifiedWriteValuesSpec::OneToToggle,
      timer2_interrupt_mode.modified_write_values.clone().unwrap()
    );
    assert_eq!(1, timer2_interrupt_mode.enumerated_value_sets.len());
    assert_eq!(
      3,
      timer2_interrupt_mode.enumerated_value_sets[0].values.len()
    );
    assert_eq!(
      "Match",
      timer2_interrupt_mode.enumerated_value_sets[0].values[0].name
    );
    assert_eq!(
      Some(EnumeratedValueValueSpec::Value(0)),
      timer2_interrupt_mode.enumerated_value_sets[0].values[0].value
    );
    assert_eq!(
      "Underflow",
      timer2_interrupt_mode.enumerated_value_sets[0].values[1].name
    );
    assert_eq!(
      Some(EnumeratedValueValueSpec::Value(1)),
      timer2_interrupt_mode.enumerated_value_sets[0].values[1].value
    );
    assert_eq!(
      "Overflow",
      timer2_interrupt_mode.enumerated_value_sets[0].values[2].name
    );
    assert_eq!(
      Some(EnumeratedValueValueSpec::Value(2)),
      timer2_interrupt_mode.enumerated_value_sets[0].values[2].value
    );

    assert_eq!(
      "RELOAD[0]",
      ds.get_register("TIMER0.RELOAD[0]").unwrap().name
    );
    assert_eq!(
      "RELOAD[1]",
      ds.get_register("TIMER0.RELOAD[1]").unwrap().name
    );
    assert_eq!(
      "RELOAD[2]",
      ds.get_register("TIMER0.RELOAD[2]").unwrap().name
    );
    assert_eq!(
      "RELOAD[3]",
      ds.get_register("TIMER0.RELOAD[3]").unwrap().name
    );

    assert_eq!(
      "RELOAD[0]",
      ds.get_register("TIMER1.RELOAD[0]").unwrap().name
    );
    assert_eq!(
      "RELOAD[1]",
      ds.get_register("TIMER1.RELOAD[1]").unwrap().name
    );
    assert_eq!(
      "RELOAD[2]",
      ds.get_register("TIMER1.RELOAD[2]").unwrap().name
    );
    assert_eq!(
      "RELOAD[3]",
      ds.get_register("TIMER1.RELOAD[3]").unwrap().name
    );

    assert_eq!(
      "RELOAD[0]",
      ds.get_register("TIMER2.RELOAD[0]").unwrap().name
    );
    assert_eq!(
      "RELOAD[1]",
      ds.get_register("TIMER2.RELOAD[1]").unwrap().name
    );
    assert_eq!(
      "RELOAD[2]",
      ds.get_register("TIMER2.RELOAD[2]").unwrap().name
    );
    assert_eq!(
      "RELOAD[3]",
      ds.get_register("TIMER2.RELOAD[3]").unwrap().name
    );
  }
}
