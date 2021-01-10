use svd_parser::{Register, RegisterInfo};

use super::field::FieldSpec;
use super::AccessSpec;
use crate::{
  clean_whitespace_opt,
  error::{SvdExpanderError, SvdExpanderResult},
  value::{EnumeratedValueSetSpec, ModifiedWriteValuesSpec, WriteConstraintSpec},
};

/// Describes a register. Registers may be top-level constructs of a peripheral or may be nested
/// within register clusters.
#[derive(Debug, Clone, PartialEq)]
pub struct RegisterSpec {
  preceding_path: String,
  derived_from: Option<String>,
  base_address: u32,

  /// Name that identifies the register. Must be unique within the scope of its parent.
  pub name: String,

  /// Description of the details of the register. May describe its purpose, operation, and effects
  /// on other parts of the device.
  pub description: Option<String>,

  /// Register's starting address relative to its parent.
  pub address_offset: u32,

  /// The bit width of the register.
  pub size: Option<u32>,

  /// The value of the register after reset.
  pub reset_value: Option<u32>,

  /// The bits of the register that have a defined reset value.
  pub reset_mask: Option<u32>,

  /// The access rights of the register.
  pub access: Option<AccessSpec>,

  /// The fields that exist on the register.
  pub fields: Vec<FieldSpec>,

  /// Default write constraints for fields on this register
  pub default_field_write_constraint: Option<WriteConstraintSpec>,

  /// Default modified write values for fields on this register
  pub default_field_modified_write_values: Option<ModifiedWriteValuesSpec>,
}
impl RegisterSpec {
  pub(crate) fn new(
    r: &Register,
    preceding_path: &str,
    base_address: u32,
  ) -> SvdExpanderResult<Vec<Self>> {
    let specs: Vec<Self> = match r {
      Register::Single(ref ri) => vec![Self::from_register_info(ri, preceding_path, base_address)?],
      Register::Array(ref fi, ref d) => {
        let dim_indices = if let Some(ref di) = d.dim_index {
          if d.dim != di.len() as u32 {
            return Err(SvdExpanderError::new(&format!(
              "Register {}: 'dim' element must have the same value as the length of 'dimIndex'",
              &r.name
            )));
          }
          di.to_owned()
        } else {
          (0..d.dim).map(|v| v.to_string()).collect()
        };

        let prototype = Self::from_register_info(fi, preceding_path, base_address)?;
        let mut register_specs = Vec::with_capacity(d.dim as usize);

        for (n, dim_index) in dim_indices.iter().enumerate() {
          let mut spec = prototype.clone();
          spec.interpolate_array_params(
            dim_index.clone(),
            prototype.address_offset + n as u32 * d.dim_increment,
          );
          register_specs.push(spec);
        }

        register_specs
      }
    };

    Ok(specs)
  }

  /// The memory address of this register
  pub fn address(&self) -> u32 {
    self.base_address + self.address_offset
  }

  /// The full path to the register that this register inherits from (if any).
  pub fn derived_from_path(&self) -> Option<String> {
    match self.derived_from {
      Some(ref df) => match df.contains(".") {
        true => Some(df.clone()),
        false => Some(format!("{}.{}", self.preceding_path, df)),
      },
      None => None,
    }
  }

  /// The full path to this register.
  pub fn path(&self) -> String {
    format!("{}.{}", self.preceding_path, self.name)
  }

  /// Iterates all the enumerated value sets on all the fields in this register.
  pub fn iter_enumerated_value_sets<'a>(
    &'a self,
  ) -> Box<dyn Iterator<Item = &EnumeratedValueSetSpec> + 'a> {
    Box::new(
      self
        .fields
        .iter()
        .flat_map(|f| f.enumerated_value_sets.iter()),
    )
  }

  pub(crate) fn clone_with_overrides(&self, preceding_path: &str, base_address: u32) -> Self {
    let mut register = Self {
      preceding_path: preceding_path.to_owned(),
      derived_from: None,
      base_address,
      name: self.name.clone(),
      description: self.description.clone(),
      address_offset: self.address_offset,
      size: self.size,
      reset_value: self.reset_value,
      reset_mask: self.reset_mask,
      access: self.access,
      fields: Vec::new(),
      default_field_write_constraint: self.default_field_write_constraint.clone(),
      default_field_modified_write_values: self.default_field_modified_write_values.clone(),
    };

    register.fields = self
      .fields
      .iter()
      .map(|f| f.clone_with_overrides(&register.path(), register.address()))
      .collect();

    register
  }

  pub(crate) fn inherit_from(&mut self, rs: &RegisterSpec) -> bool {
    let mut changed = false;

    if self.description.is_none() && rs.description.is_some() {
      self.description = rs.description.clone();
      changed = true;
    }

    if self.size.is_none() && rs.size.is_some() {
      self.size = rs.size;
      changed = true;
    }

    if self.access.is_none() && rs.access.is_some() {
      self.access = rs.access;
      changed = true;
    }

    if self.reset_value.is_none() && rs.reset_value.is_some() {
      self.reset_value = rs.reset_value;
      changed = true;
    }

    if self.reset_mask.is_none() && rs.reset_mask.is_some() {
      self.reset_mask = rs.reset_mask;
      changed = true;
    }

    if self.default_field_write_constraint.is_none() && rs.default_field_write_constraint.is_some()
    {
      self.default_field_write_constraint = rs.default_field_write_constraint.clone();
      changed = true;
    }

    if self.default_field_modified_write_values.is_none()
      && rs.default_field_modified_write_values.is_some()
    {
      self.default_field_modified_write_values = rs.default_field_modified_write_values.clone();
      changed = true;
    }

    for ancestor in rs.fields.iter() {
      if let Some(ref mut descendant) = self.fields.iter_mut().find(|f| f.name == ancestor.name) {
        if descendant.inherit_from(ancestor) {
          changed = true;
        }
      } else {
        self
          .fields
          .push(ancestor.clone_with_overrides(&self.path(), self.address()));
        changed = true;
      }
    }

    changed
  }

  pub(crate) fn propagate_default_properties(
    &mut self,
    size: &Option<u32>,
    reset_value: &Option<u32>,
    reset_mask: &Option<u32>,
    access: &Option<AccessSpec>,
  ) -> bool {
    let mut changed = false;

    if self.size.is_none() && size.is_some() {
      self.size = size.clone();
      changed = true;
    }

    if self.reset_value.is_none() && reset_value.is_some() {
      self.reset_value = reset_value.clone();
      changed = true;
    }

    if self.reset_mask.is_none() && reset_mask.is_some() {
      self.reset_mask = reset_mask.clone();
      changed = true;
    }

    if self.access.is_none() && access.is_some() {
      self.access = access.clone();
      changed = true;
    }

    for field in self.fields.iter_mut() {
      if field.propagate_default_properties(
        &self.access,
        &self.default_field_write_constraint,
        &self.default_field_modified_write_values,
        &self.reset_mask,
        &self.reset_value,
      ) {
        changed = true;
      }
    }

    changed
  }

  pub(crate) fn mutate_fields<F>(&mut self, f: F) -> SvdExpanderResult<bool>
  where
    F: Fn(&mut FieldSpec) -> SvdExpanderResult<bool>,
    F: Copy,
  {
    let mut changed = false;

    for field in self.fields.iter_mut() {
      if f(field)? {
        changed = true
      }
    }

    Ok(changed)
  }

  pub(crate) fn mutate_enumerated_value_sets<F>(&mut self, f: F) -> SvdExpanderResult<bool>
  where
    F: Fn(&mut EnumeratedValueSetSpec) -> SvdExpanderResult<bool>,
    F: Copy,
  {
    let mut changed = false;

    for field in &mut self.fields.iter_mut() {
      if field.mutate_enumerate_value_sets(f)? {
        changed = true;
      }
    }

    Ok(changed)
  }

  fn from_register_info(
    ri: &RegisterInfo,
    preceding_path: &str,
    base_address: u32,
  ) -> SvdExpanderResult<Self> {
    let mut register = Self {
      preceding_path: preceding_path.to_owned(),
      derived_from: ri.derived_from.clone(),
      base_address,
      name: ri.name.clone(),
      description: clean_whitespace_opt(ri.description.clone())?,
      address_offset: ri.address_offset,
      size: ri.size.clone(),
      reset_value: ri.reset_value.clone(),
      reset_mask: ri.reset_mask.clone(),
      access: match ri.access {
        Some(ref a) => Some(AccessSpec::new(a)),
        None => None,
      },
      fields: Vec::new(),
      default_field_write_constraint: match ri.write_constraint {
        Some(ref wc) => Some(WriteConstraintSpec::new(wc)),
        None => None,
      },
      default_field_modified_write_values: match ri.modified_write_values {
        Some(ref mwv) => Some(ModifiedWriteValuesSpec::new(mwv)),
        None => None,
      },
    };

    register.fields = {
      let mut field_specs: Vec<FieldSpec> = Vec::new();

      if let Some(ref fields) = ri.fields {
        for f in fields.iter() {
          field_specs.extend(FieldSpec::new(f, &register.path(), register.address())?);
        }
      }

      field_specs
    };

    Ok(register)
  }

  fn interpolate_array_params(&mut self, index: String, address_offset: u32) {
    self.name = self.name.replace("%s", &index);

    if let Some(df) = self.derived_from.clone() {
      self.derived_from = Some(df.replace("%s", &index));
    }

    if let Some(desc) = self.description.clone() {
      self.description = Some(desc.replace("%s", &index));
    }

    self.address_offset = address_offset;

    let self_address = self.address();
    for field in self.fields.iter_mut() {
      field.base_address = self_address;
    }

    let self_path = self.path();
    for field in self.fields.iter_mut() {
      field.preceding_path = self_path.clone();
    }
  }
}

#[cfg(test)]
mod tests {
  use super::{AccessSpec, RegisterSpec};
  use crate::value::{ModifiedWriteValuesSpec, WriteConstraintRangeSpec, WriteConstraintSpec};
  use std::cell::RefCell;
  use svd_parser::parse::Parse;
  use svd_parser::Register;
  use xmltree::Element;

  #[test]
  fn can_create_single_from_xml() {
    let el: Element = Element::parse(
      r##"
      <register>
        <name>FOO</name>
        <description>Bar</description>
        <addressOffset>3000</addressOffset>
        <access>write-only</access>
        <resetValue>1234</resetValue>
        <resetMask>4321</resetMask>
        <size>16</size>
        <writeConstraint>
          <range>
            <minimum>2</minimum>
            <maximum>4</maximum>
          </range>
        </writeConstraint>
        <modifiedWriteValues>zeroToToggle</modifiedWriteValues>
        <fields>
          <field>
            <name>F1</name>
            <bitWidth>2</bitWidth>
            <bitOffset>0</bitOffset>
          </field>
          <field>
            <name>F2</name>
            <bitWidth>2</bitWidth>
            <bitOffset>2</bitOffset>
          </field>
        </fields>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Register::parse(&el).unwrap();

    let mut specs = RegisterSpec::new(&ri, "", 0).unwrap();

    assert_eq!(1, specs.len());

    let rs = specs.pop().unwrap();

    assert_eq!("FOO", rs.name);
    assert_eq!("Bar", rs.description.unwrap());
    assert_eq!(3000, rs.address_offset);
    assert_eq!(AccessSpec::WriteOnly, rs.access.unwrap());
    assert_eq!(1234, rs.reset_value.unwrap());
    assert_eq!(4321, rs.reset_mask.unwrap());
    assert_eq!(16, rs.size.unwrap());
    assert_eq!(
      WriteConstraintSpec::Range(WriteConstraintRangeSpec { min: 2, max: 4 }),
      rs.default_field_write_constraint.unwrap()
    );
    assert_eq!(
      ModifiedWriteValuesSpec::ZeroToToggle,
      rs.default_field_modified_write_values.unwrap()
    );

    assert_eq!(2, rs.fields.len());
    assert_eq!("F1", rs.fields[0].name);
    assert_eq!("F2", rs.fields[1].name);
  }

  #[test]
  fn can_create_multiple_from() {
    let el: Element = Element::parse(
      r##"
      <register>
        <name>FOO_%s</name>
        <description>Bar %s</description>
        <addressOffset>3000</addressOffset>
        <access>write-only</access>
        <resetValue>1234</resetValue>
        <resetMask>4321</resetMask>
        <size>16</size>
        <dim>3</dim>
        <dimIndex>one,two,three</dimIndex>
        <dimIncrement>0x20</dimIncrement>
        <fields>
          <field>
            <name>F1</name>
            <bitWidth>2</bitWidth>
            <bitOffset>0</bitOffset>
          </field>
          <field>
            <name>F2</name>
            <bitWidth>2</bitWidth>
            <bitOffset>2</bitOffset>
          </field>
        </fields>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Register::parse(&el).unwrap();

    let mut specs = RegisterSpec::new(&ri, "", 0).unwrap();

    assert_eq!(3, specs.len());

    let mut rs = specs.pop().unwrap();

    assert_eq!("FOO_three", rs.name);
    assert_eq!("Bar three", rs.description.unwrap());
    assert_eq!(3064, rs.address_offset);
    assert_eq!(AccessSpec::WriteOnly, rs.access.unwrap());
    assert_eq!(1234, rs.reset_value.unwrap());
    assert_eq!(4321, rs.reset_mask.unwrap());
    assert_eq!(16, rs.size.unwrap());
    assert_eq!(2, rs.fields.len());
    assert_eq!("F1", rs.fields[0].name);
    assert_eq!("F2", rs.fields[1].name);

    rs = specs.pop().unwrap();

    assert_eq!("FOO_two", rs.name);
    assert_eq!("Bar two", rs.description.unwrap());
    assert_eq!(3032, rs.address_offset);
    assert_eq!(AccessSpec::WriteOnly, rs.access.unwrap());
    assert_eq!(1234, rs.reset_value.unwrap());
    assert_eq!(4321, rs.reset_mask.unwrap());
    assert_eq!(16, rs.size.unwrap());
    assert_eq!(2, rs.fields.len());
    assert_eq!("F1", rs.fields[0].name);
    assert_eq!("F2", rs.fields[1].name);

    rs = specs.pop().unwrap();

    assert_eq!("FOO_one", rs.name);
    assert_eq!("Bar one", rs.description.unwrap());
    assert_eq!(3000, rs.address_offset);
    assert_eq!(AccessSpec::WriteOnly, rs.access.unwrap());
    assert_eq!(1234, rs.reset_value.unwrap());
    assert_eq!(4321, rs.reset_mask.unwrap());
    assert_eq!(16, rs.size.unwrap());
    assert_eq!(2, rs.fields.len());
    assert_eq!("F1", rs.fields[0].name);
    assert_eq!("F2", rs.fields[1].name);
  }

  #[test]
  fn inherits_from_other_register() {
    let descendant_el: Element = Element::parse(
      r##"
      <register>
        <name>FOO</name>
        <addressOffset>3000</addressOffset>
        <fields>
          <field>
            <name>F2</name>
            <description>Qux</description>
            <bitWidth>3</bitWidth>
            <bitOffset>2</bitOffset>
            <access>write-only</access>
          </field>
          <field>
            <name>F3</name>
            <description>Abc</description>
            <bitWidth>4</bitWidth>
            <bitOffset>5</bitOffset>
            <access>read-write</access>
          </field>
          <field>
            <name>F1</name>
            <bitWidth>2</bitWidth>
            <bitOffset>0</bitOffset>
          </field>
        </fields>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_ri = Register::parse(&descendant_el).unwrap();
    let mut descendant_specs = RegisterSpec::new(&descendant_ri, "", 0).unwrap();
    let mut descendant_rs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <register>
        <name>FOO2</name>
        <description>Baz</description>
        <addressOffset>4000</addressOffset>
        <access>read-only</access>
        <resetValue>2345</resetValue>
        <resetMask>5432</resetMask>
        <size>24</size>
        <writeConstraint>
          <range>
            <minimum>2</minimum>
            <maximum>4</maximum>
          </range>
        </writeConstraint>
        <modifiedWriteValues>zeroToToggle</modifiedWriteValues>
        <fields>
          <field>
            <name>F1</name>
            <description>Baz</description>
            <bitWidth>3</bitWidth>
            <bitOffset>2</bitOffset>
            <access>read-only</access>
          </field>
          <field>
            <name>F4</name>
            <description>Def</description>
            <bitWidth>6</bitWidth>
            <bitOffset>7</bitOffset>
            <access>read-only</access>
          </field>
          <field>
            <name>F2</name>
            <description>corge</description>
            <bitWidth>2</bitWidth>
            <bitOffset>0</bitOffset>
            <access>read-only</access>
          </field>
        </fields>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_ri = Register::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = RegisterSpec::new(&ancestor_ri, "", 0).unwrap();
    let ancestor_rs = ancestor_specs.pop().unwrap();

    let changed = descendant_rs.inherit_from(&ancestor_rs);

    assert!(changed);

    // Not inherited
    assert_eq!("FOO", descendant_rs.name);
    assert_eq!(3000, descendant_rs.address_offset);

    // Inherited
    assert_eq!("Baz", descendant_rs.description.unwrap());
    assert_eq!(AccessSpec::ReadOnly, descendant_rs.access.unwrap());
    assert_eq!(2345, descendant_rs.reset_value.unwrap());
    assert_eq!(5432, descendant_rs.reset_mask.unwrap());
    assert_eq!(24, descendant_rs.size.unwrap());
    assert_eq!(
      WriteConstraintSpec::Range(WriteConstraintRangeSpec { min: 2, max: 4 }),
      descendant_rs.default_field_write_constraint.unwrap()
    );
    assert_eq!(
      ModifiedWriteValuesSpec::ZeroToToggle,
      descendant_rs.default_field_modified_write_values.unwrap()
    );

    assert_eq!(4, descendant_rs.fields.len());

    let f1 = descendant_rs
      .fields
      .iter()
      .find(|f| f.name == "F1")
      .unwrap();

    let f2 = descendant_rs
      .fields
      .iter()
      .find(|f| f.name == "F2")
      .unwrap();

    let f3 = descendant_rs
      .fields
      .iter()
      .find(|f| f.name == "F3")
      .unwrap();

    let f4 = descendant_rs
      .fields
      .iter()
      .find(|f| f.name == "F4")
      .unwrap();

    assert_eq!("F1", f1.name);
    assert_eq!("Baz", f1.description.clone().unwrap());
    assert_eq!(2, f1.width);
    assert_eq!(0, f1.offset);
    assert_eq!(AccessSpec::ReadOnly, f1.access.unwrap());

    assert_eq!("F2", f2.name);
    assert_eq!("Qux", f2.description.clone().unwrap());
    assert_eq!(3, f2.width);
    assert_eq!(2, f2.offset);
    assert_eq!(AccessSpec::WriteOnly, f2.access.unwrap());

    assert_eq!("F3", f3.name);
    assert_eq!("Abc", f3.description.clone().unwrap());
    assert_eq!(4, f3.width);
    assert_eq!(5, f3.offset);
    assert_eq!(AccessSpec::ReadWrite, f3.access.unwrap());

    assert_eq!("F4", f4.name);
    assert_eq!("Def", f4.description.clone().unwrap());
    assert_eq!(6, f4.width);
    assert_eq!(7, f4.offset);
    assert_eq!(AccessSpec::ReadOnly, f4.access.unwrap());
  }

  #[test]
  fn inherits_from_returns_false_when_no_changes() {
    let descendant_el: Element = Element::parse(
      r##"
      <register>
        <name>FOO</name>
        <description>BAR</description>
        <addressOffset>3000</addressOffset>
        <access>read-write</access>
        <resetValue>1234</resetValue>
        <resetMask>4321</resetMask>
        <size>16</size>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_ri = Register::parse(&descendant_el).unwrap();
    let mut descendant_specs = RegisterSpec::new(&descendant_ri, "", 0).unwrap();
    let mut descendant_rs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <register>
        <name>FOO2</name>
        <description>Baz</description>
        <addressOffset>4000</addressOffset>
        <access>read-only</access>
        <resetValue>2345</resetValue>
        <resetMask>5432</resetMask>
        <size>24</size>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_ri = Register::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = RegisterSpec::new(&ancestor_ri, "", 0).unwrap();
    let ancestor_rs = ancestor_specs.pop().unwrap();

    let changed = descendant_rs.inherit_from(&ancestor_rs);

    assert!(!changed);

    // Not inherited
    assert_eq!("FOO", descendant_rs.name);
    assert_eq!("BAR", descendant_rs.description.unwrap());
    assert_eq!(3000, descendant_rs.address_offset);
    assert_eq!(AccessSpec::ReadWrite, descendant_rs.access.unwrap());
    assert_eq!(1234, descendant_rs.reset_value.unwrap());
    assert_eq!(4321, descendant_rs.reset_mask.unwrap());
    assert_eq!(16, descendant_rs.size.unwrap());
  }

  #[test]
  fn inherits_from_returns_true_for_overridden_inherited_field() {
    let descendant_el: Element = Element::parse(
      r##"
      <register>
        <name>FOO</name>
        <addressOffset>3000</addressOffset>
        <fields>
          <field>
            <name>F1</name>
            <bitOffset>2</bitOffset>
            <bitWidth>1</bitWidth>
          </field>
        </fields>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_ri = Register::parse(&descendant_el).unwrap();
    let mut descendant_specs = RegisterSpec::new(&descendant_ri, "", 0).unwrap();
    let mut descendant_rs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <register>
        <name>FOO2</name>
        <addressOffset>4000</addressOffset>
        <fields>
          <field>
            <name>F1</name>
            <description>BAR</description>
            <bitOffset>2</bitOffset>
            <bitWidth>1</bitWidth>
          </field>
        </fields>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_ri = Register::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = RegisterSpec::new(&ancestor_ri, "", 0).unwrap();
    let ancestor_rs = ancestor_specs.pop().unwrap();

    let changed = descendant_rs.inherit_from(&ancestor_rs);

    assert!(changed);
    assert_eq!(1, descendant_rs.fields.len());
  }

  #[test]
  fn inherits_from_returns_true_for_added_inherited_field() {
    let descendant_el: Element = Element::parse(
      r##"
      <register>
        <name>FOO</name>
        <addressOffset>3000</addressOffset>
        <fields>
          <field>
            <name>F1</name>
            <bitOffset>2</bitOffset>
            <bitWidth>1</bitWidth>
          </field>
        </fields>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_ri = Register::parse(&descendant_el).unwrap();
    let mut descendant_specs = RegisterSpec::new(&descendant_ri, "", 0).unwrap();
    let mut descendant_rs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <register>
        <name>FOO2</name>
        <addressOffset>4000</addressOffset>
        <fields>
          <field>
            <name>F2</name>
            <bitOffset>2</bitOffset>
            <bitWidth>1</bitWidth>
          </field>
        </fields>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_ri = Register::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = RegisterSpec::new(&ancestor_ri, "", 0).unwrap();
    let ancestor_rs = ancestor_specs.pop().unwrap();

    let changed = descendant_rs.inherit_from(&ancestor_rs);

    assert!(changed);
    assert_eq!(2, descendant_rs.fields.len());
  }

  #[test]
  fn single_has_correct_path() {
    let el: Element = Element::parse(
      r##"
      <register>
        <name>FOO</name>
        <addressOffset>3000</addressOffset>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Register::parse(&el).unwrap();
    let rs = RegisterSpec::new(&ri, "path", 0).unwrap();

    assert_eq!("path.FOO", rs[0].path());
  }

  #[test]
  fn multiples_have_correct_paths() {
    let el: Element = Element::parse(
      r##"
      <register>
        <name>FOO_%s</name>
        <addressOffset>3000</addressOffset>
        <dim>3</dim>
        <dimIndex>one,two,three</dimIndex>
        <dimIncrement>0x4</dimIncrement>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Register::parse(&el).unwrap();
    let rs = RegisterSpec::new(&ri, "path", 0).unwrap();

    assert_eq!("path.FOO_one", rs[0].path());
    assert_eq!("path.FOO_two", rs[1].path());
    assert_eq!("path.FOO_three", rs[2].path());
  }

  #[test]
  fn single_has_correct_derived_from_path() {
    let el: Element = Element::parse(
      r##"
      <register derivedFrom="BAR">
        <name>FOO</name>
        <addressOffset>3000</addressOffset>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Register::parse(&el).unwrap();
    let rs = RegisterSpec::new(&ri, "path", 0).unwrap();

    assert_eq!("path.BAR", rs[0].derived_from_path().unwrap());
  }

  #[test]
  fn multiples_have_correct_derived_from_paths() {
    let el: Element = Element::parse(
      r##"
      <register derivedFrom="BAR_%s">
        <name>FOO_%s</name>
        <addressOffset>3000</addressOffset>
        <dim>3</dim>
        <dimIndex>one,two,three</dimIndex>
        <dimIncrement>0x4</dimIncrement>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Register::parse(&el).unwrap();
    let rs = RegisterSpec::new(&ri, "path", 0).unwrap();

    assert_eq!("path.BAR_one", rs[0].derived_from_path().unwrap());
    assert_eq!("path.BAR_two", rs[1].derived_from_path().unwrap());
    assert_eq!("path.BAR_three", rs[2].derived_from_path().unwrap());
  }

  #[test]
  fn mutates_fields() {
    let el: Element = Element::parse(
      r##"
      <register>
        <name>FOO</name>
        <addressOffset>5000</addressOffset>
        <fields>
          <field>
            <name>FOO1</name>
            <bitOffset>1</bitOffset>
            <bitWidth>1</bitWidth>
          </field>
          <field>
            <name>FOO2</name>
            <bitOffset>2</bitOffset>
            <bitWidth>1</bitWidth>
          </field>
        </fields>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Register::parse(&el).unwrap();
    let mut rs = RegisterSpec::new(&ri, "path", 0).unwrap();

    let top = &mut rs[0];
    let count = RefCell::new(0);

    top
      .mutate_fields(|f| {
        f.name = format!("{} {}", f.name, count.borrow());
        let current = (*count.borrow()).clone();
        *count.borrow_mut() = current + 1;
        Ok(false)
      })
      .unwrap();

    assert_eq!("FOO1 0", top.fields[0].name);
    assert_eq!("FOO2 1", top.fields[1].name);
  }

  #[test]
  pub fn propagates_default_register_properties() {
    let el: Element = Element::parse(
      r##"
      <register>
        <name>FOO</name>
        <addressOffset>5000</addressOffset>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Register::parse(&el).unwrap();
    let mut rs = RegisterSpec::new(&ri, "path", 0).unwrap();
    let register = &mut rs[0];

    let changed = register.propagate_default_properties(
      &Some(1),
      &Some(2),
      &Some(3),
      &Some(AccessSpec::ReadWriteOnce),
    );

    assert!(changed);
    assert_eq!(1, register.size.unwrap());
    assert_eq!(2, register.reset_value.unwrap());
    assert_eq!(3, register.reset_mask.unwrap());
    assert_eq!(AccessSpec::ReadWriteOnce, register.access.unwrap());
  }

  #[test]
  pub fn propagate_default_register_properties_returns_false_when_no_changes() {
    let el: Element = Element::parse(
      r##"
      <register>
        <name>FOO</name>
        <addressOffset>5000</addressOffset>
      </register>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Register::parse(&el).unwrap();
    let mut rs = RegisterSpec::new(&ri, "path", 0).unwrap();
    let register = &mut rs[0];

    let changed = register.propagate_default_properties(&None, &None, &None, &None);

    assert!(!changed);
    assert!(register.access.is_none());
    assert!(register.reset_value.is_none());
    assert!(register.reset_mask.is_none());
    assert!(register.size.is_none());
  }
}
