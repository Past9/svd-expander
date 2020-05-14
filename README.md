[![crates.io](https://img.shields.io/crates/d/svd-expander.svg)](https://crates.io/crates/svd-expander)
[![crates.io](https://img.shields.io/crates/v/svd-expander.svg)](https://crates.io/crates/svd-expander)
[![Documentation](https://docs.rs/svd-expander/badge.svg)](https://docs.rs/svd-expander)
[![Rust CI](https://github.com/Past9/svd-expander/workflows/Rust/badge.svg?branch=master)](https://github.com/Past9/svd-expander/actions?query=workflow%3ARust+branch%3Amaster)

# `svd-expander`

Expands arrays and resolves inheritance chains in CMSIS-SVD specifications.

## Example usage:

```rust
use svd_expander::DeviceSpec;

fn main() {
  let xml = r##"
  <device>
    <name>CORTEX_DEVICE</name>
    <peripherals>

      <peripheral>
        <name>GPIOA</name>
        <baseAddress>0x40010000</baseAddress>
        <registers>
          <register>
            <name>IDR</name>
            <description>Input Data Register</description>
            <addressOffset>0x00</addressOffset>
            <fields>

              <!-- 
                This field is a template that will be expanded 
                out to 16 input fields named D1 through D16.
              -->

              <field>
                <name>D%s</name>
                <bitWidth>1</bitWidth>
                <bitOffset>0</bitOffset>
                <dim>16</dim>
                <dimIndex>1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16</dimIndex>
                <dimIncrement>1</dimIncrement>
              </field>

            </fields>
          </register>
        </registers>
      </peripheral>

      <!-- 
        GPIOA will be copied to make GPIOB below, which is identical 
        except for any overridden properties (just name and 
        baseAddress in this case).
      -->

      <peripheral derivedFrom="GPIOA">
        <name>GPIOB</name>
        <baseAddress>0x40010100</baseAddress>
      </peripheral>

    </peripherals>
  </device>
  "##;

  let device = DeviceSpec::from_xml(xml).unwrap();

  // The IDR register on GPIOA has been expanded to 16 fields.
  assert_eq!(16, device.get_register("GPIOA.IDR").unwrap().fields.len());

  // Those fields each had their bit offset (location in the register)
  // incremented appropriately.
  assert_eq!(0, device.get_field("GPIOA.IDR.D1").unwrap().offset);
  assert_eq!(1, device.get_field("GPIOA.IDR.D2").unwrap().offset);
  // ...etc...
  assert_eq!(9, device.get_field("GPIOA.IDR.D10").unwrap().offset);
  // ...etc...

  // GPIOB also has an IDR register with 16 fields, which was inherited 
  // from GPIOA.
  assert_eq!(16, device.get_register("GPIOB.IDR").unwrap().fields.len());

  // GPIOB kept its name and base address when it inherited properties
  // from GPIOA.
  assert_eq!("GPIOB", device.get_peripheral("GPIOB").unwrap().name);
  assert_eq!(0x40010100, device.get_peripheral("GPIOB").unwrap().base_address);

}
```

This crate is intended for use in code generators. It is under active development and bug
reports are welcome.

Feature requests may be considered, but [svd-expander](https://crates.io/crates/svd-expander)
depends on [svd-parser](https://crates.io/crates/svd-parser) (at least for now) to parse the
SVD files, so it can only implement the features supported by the parser.