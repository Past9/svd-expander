use svd_parser::{Field, FieldInfo};

use super::AccessSpec;
use crate::{
  clean_whitespace_opt,
  error::{SvdExpanderError, SvdExpanderResult},
  value::{EnumeratedValueSetSpec, ModifiedWriteValuesSpec, WriteConstraintSpec},
  EnumeratedValueUsageSpec,
};

/// Describes a field on a register.
#[derive(Debug, Clone, PartialEq)]
pub struct FieldSpec {
  preceding_path: String,
  derived_from: Option<String>,
  base_address: u32,

  /// A name that identfies the field. Must be unique within the parent register.
  pub name: String,

  /// Description of the field's usage, purpose, and/or operation.
  pub description: Option<String>,

  /// The position of the least-significant bit of this field within its register.
  pub offset: u32,

  /// The bit width of the field.
  pub width: u32,

  /// The access rights to the field.
  pub access: Option<AccessSpec>,

  /// Constraints for writing values to the field.
  pub write_constraint: Option<WriteConstraintSpec>,

  /// Describes the manipulation of data written to this field. If `None`, the value written to
  /// the field is the value stored in the field.
  pub modified_write_values: Option<ModifiedWriteValuesSpec>,

  pub enumerated_value_sets: Vec<EnumeratedValueSetSpec>,

  pub reset_value: Option<u32>,

  pub reset_mask: Option<u32>,
}
impl FieldSpec {
  pub(crate) fn new(
    f: &Field,
    preceding_path: &str,
    base_address: u32,
  ) -> SvdExpanderResult<Vec<Self>> {
    let specs: Vec<Self> = match f {
      Field::Single(ref fi) => vec![Self::from_field_info(fi, preceding_path, base_address)?],
      Field::Array(ref fi, ref d) => {
        let dim_indices = if let Some(ref di) = d.dim_index {
          if d.dim != di.len() as u32 {
            return Err(SvdExpanderError::new(&format!(
              "Field {}: 'dim' element must have the same value as the length of 'dimIndex'",
              &f.name
            )));
          }
          di.to_owned()
        } else {
          (0..d.dim).map(|v| v.to_string()).collect()
        };

        let prototype = Self::from_field_info(fi, preceding_path, base_address)?;
        let mut field_specs = Vec::with_capacity(d.dim as usize);

        for (n, dim_index) in dim_indices.iter().enumerate() {
          let mut spec = prototype.clone();
          spec.interpolate_array_params(
            dim_index.clone(),
            prototype.offset + n as u32 * d.dim_increment,
          );
          field_specs.push(spec);
        }

        field_specs
      }
    };

    Ok(specs)
  }

  /// Returns the first enumerated value set that allows both reading and writing, if any.
  pub fn read_write_value_set(&self) -> Option<EnumeratedValueSetSpec> {
    for set in self.enumerated_value_sets.iter() {
      if set.usage() == EnumeratedValueUsageSpec::ReadWrite {
        return Some(set.clone());
      }
    }
    None
  }

  /// Returns the first enumerated value set that only allows reading, if any.
  pub fn read_only_value_set(&self) -> Option<EnumeratedValueSetSpec> {
    for set in self.enumerated_value_sets.iter() {
      if set.usage() == EnumeratedValueUsageSpec::Read {
        return Some(set.clone());
      }
    }
    None
  }

  /// Returns the first readable enumerated value set, if any.
  pub fn readable_value_set(&self) -> Option<EnumeratedValueSetSpec> {
    for set in self.enumerated_value_sets.iter() {
      if set.usage().can_read() {
        return Some(set.clone());
      }
    }
    None
  }

  /// Returns the first enumerated value set that only allows writing, if any.
  pub fn write_only_value_set(&self) -> Option<EnumeratedValueSetSpec> {
    for set in self.enumerated_value_sets.iter() {
      if set.usage() == EnumeratedValueUsageSpec::Write {
        return Some(set.clone());
      }
    }
    None
  }

  /// Returns the first writable enumerated value set, if any.
  pub fn writable_value_set(&self) -> Option<EnumeratedValueSetSpec> {
    for set in self.enumerated_value_sets.iter() {
      if set.usage().can_write() {
        return Some(set.clone());
      }
    }
    None
  }

  /// Whether this field is readable
  pub fn can_read(&self) -> bool {
    match self.access {
      Some(a) => a.can_read(),
      None => true, // Default access is read-write
    }
  }

  /// Whether this field is writable
  pub fn can_write(&self) -> bool {
    match self.access {
      Some(a) => a.can_write(),
      None => true, // Default access is read-write
    }
  }

  /// The bit mask for reading/writing this field on the parent register
  pub fn mask(&self) -> u32 {
    u32::MAX >> (32 - self.width) << self.offset
  }

  /// The memory address of this field's parent register
  pub fn address(&self) -> u32 {
    self.base_address
  }

  /// The full path to the field that this field inherits from (if any).
  pub fn derived_from_path(&self) -> Option<String> {
    match self.derived_from {
      Some(ref df) => match df.contains(".") {
        true => Some(df.clone()),
        false => Some(format!("{}.{}", self.preceding_path, df)),
      },
      None => None,
    }
  }

  /// The full path to this field.
  pub fn path(&self) -> String {
    format!("{}.{}", self.preceding_path, self.name)
  }

  pub fn parent_path(&self) -> String {
    self.preceding_path.clone()
  }

  pub(crate) fn clone_with_overrides(&self, preceding_path: &str, base_address: u32) -> Self {
    let mut field = Self {
      preceding_path: preceding_path.to_owned(),
      derived_from: None,
      base_address,
      name: self.name.clone(),
      description: self.description.clone(),
      offset: self.offset,
      width: self.width,
      access: self.access,
      write_constraint: self.write_constraint.clone(),
      modified_write_values: self.modified_write_values.clone(),
      enumerated_value_sets: Vec::new(),
      reset_value: None,
      reset_mask: None,
    };

    field.enumerated_value_sets = self
      .enumerated_value_sets
      .iter()
      .map(|s| s.clone_with_overridess(&field.path(), &field.preceding_path))
      .collect();

    field
  }

  pub(crate) fn inherit_from(&mut self, fs: &FieldSpec) -> bool {
    let mut changed = false;

    if self.description.is_none() && fs.description.is_some() {
      self.description = fs.description.clone();
      changed = true;
    }

    if self.access.is_none() && fs.access.is_some() {
      self.access = fs.access;
      changed = true
    }

    if self.write_constraint.is_none() && fs.write_constraint.is_some() {
      self.write_constraint = fs.write_constraint.clone();
      changed = true;
    }

    if self.modified_write_values.is_none() && fs.modified_write_values.is_some() {
      self.modified_write_values = fs.modified_write_values.clone();
      changed = true;
    }

    changed
  }

  pub(crate) fn propagate_default_properties(
    &mut self,
    access: &Option<AccessSpec>,
    write_constraint: &Option<WriteConstraintSpec>,
    modified_write_values: &Option<ModifiedWriteValuesSpec>,
    register_reset_mask: &Option<u32>,
    register_reset_value: &Option<u32>,
  ) -> bool {
    let mut changed = false;

    if self.access.is_none() && access.is_some() {
      self.access = access.clone();
      changed = true;
    }

    if self.write_constraint.is_none() && write_constraint.is_some() {
      self.write_constraint = write_constraint.clone();
      changed = true;
    }

    if self.modified_write_values.is_none() && modified_write_values.is_some() {
      self.modified_write_values = modified_write_values.clone();
      changed = true;
    }

    match (self.reset_mask, register_reset_mask) {
      (None, Some(rrm)) => {
        self.reset_mask = Some(rrm & self.mask());
        changed = true;
      }
      _ => {}
    };

    match (self.reset_value, register_reset_value) {
      (None, Some(rrv)) => {
        self.reset_value = Some((rrv & self.mask()) >> self.offset);
        changed = true;
      }
      _ => {}
    };

    changed
  }

  pub(crate) fn mutate_enumerate_value_sets<F>(&mut self, f: F) -> SvdExpanderResult<bool>
  where
    F: Fn(&mut EnumeratedValueSetSpec) -> SvdExpanderResult<bool>,
    F: Copy,
  {
    let mut changed = false;

    for set in self.enumerated_value_sets.iter_mut() {
      if f(set)? {
        changed = true
      }
    }

    Ok(changed)
  }

  fn from_field_info(
    fi: &FieldInfo,
    preceding_path: &str,
    base_address: u32,
  ) -> SvdExpanderResult<Self> {
    let mut field = Self {
      preceding_path: preceding_path.to_owned(),
      derived_from: fi.derived_from.clone(),
      base_address,
      name: fi.name.clone(),
      description: clean_whitespace_opt(fi.description.clone())?,
      offset: fi.bit_range.offset,
      width: fi.bit_range.width,
      access: match fi.access {
        Some(ref a) => Some(AccessSpec::new(a)),
        None => None,
      },
      write_constraint: match fi.write_constraint {
        Some(ref wc) => Some(WriteConstraintSpec::new(wc)),
        None => None,
      },
      modified_write_values: match fi.modified_write_values {
        Some(ref mwv) => Some(ModifiedWriteValuesSpec::new(mwv)),
        None => None,
      },
      enumerated_value_sets: Vec::new(),
      reset_value: None,
      reset_mask: None,
    };

    field.enumerated_value_sets = fi
      .enumerated_values
      .iter()
      .map(|v| EnumeratedValueSetSpec::new(v, &field.path(), &field.preceding_path))
      .collect::<SvdExpanderResult<Vec<EnumeratedValueSetSpec>>>()?;

    Ok(field)
  }

  fn interpolate_array_params(&mut self, index: String, offset: u32) {
    self.name = self.name.replace("%s", &index);

    if let Some(df) = self.derived_from.clone() {
      self.derived_from = Some(df.replace("%s", &index));
    }

    if let Some(desc) = self.description.clone() {
      self.description = Some(desc.replace("%s", &index));
    }

    self.offset = offset
  }
}

#[cfg(test)]
mod tests {
  use super::{AccessSpec, FieldSpec};
  use crate::value::{ModifiedWriteValuesSpec, WriteConstraintRangeSpec, WriteConstraintSpec};
  use svd_parser::parse::Parse;
  use svd_parser::Field;
  use xmltree::Element;

  #[test]
  fn can_create_single_from_xml() {
    let el: Element = Element::parse(
      r##"
      <field>
        <name>FOO</name>
        <description>Bar</description>
        <bitOffset>2</bitOffset>
        <bitWidth>1</bitWidth>
        <access>write-only</access>
        <writeConstraint>
          <range>
            <minimum>2</minimum>
            <maximum>4</maximum>
          </range>
        </writeConstraint>
        <modifiedWriteValues>zeroToToggle</modifiedWriteValues>
      </field>
      "##
        .as_bytes(),
    )
    .unwrap();

    let fi = Field::parse(&el).unwrap();

    let mut specs = FieldSpec::new(&fi, "", 0).unwrap();

    assert_eq!(1, specs.len());

    let fs = specs.pop().unwrap();

    assert_eq!("FOO", fs.name);
    assert_eq!("Bar", fs.description.unwrap());
    assert_eq!(1, fs.width);
    assert_eq!(2, fs.offset);
    assert_eq!(AccessSpec::WriteOnly, fs.access.unwrap());
    assert_eq!(
      WriteConstraintSpec::Range(WriteConstraintRangeSpec { min: 2, max: 4 }),
      fs.write_constraint.unwrap()
    );
    assert_eq!(
      ModifiedWriteValuesSpec::ZeroToToggle,
      fs.modified_write_values.unwrap()
    );
  }

  #[test]
  fn can_create_multiple_from_field_xml() {
    let el: Element = Element::parse(
      r##"
      <field>
        <name>FOO_%s</name>
        <description>Bar %s</description>
        <bitOffset>2</bitOffset>
        <bitWidth>1</bitWidth>
        <access>write-only</access>
        <dim>3</dim>
        <dimIndex>one,two,three</dimIndex>
        <dimIncrement>0x4</dimIncrement>
      </field>
    "##
        .as_bytes(),
    )
    .unwrap();

    let fi = Field::parse(&el).unwrap();

    let mut specs = FieldSpec::new(&fi, "", 0).unwrap();

    assert_eq!(3, specs.len());

    let mut fs = specs.pop().unwrap();

    assert_eq!("FOO_three", fs.name);
    assert_eq!("Bar three", fs.description.unwrap());
    assert_eq!(1, fs.width);
    assert_eq!(10, fs.offset);
    assert_eq!(AccessSpec::WriteOnly, fs.access.unwrap());

    fs = specs.pop().unwrap();

    assert_eq!("FOO_two", fs.name);
    assert_eq!("Bar two", fs.description.unwrap());
    assert_eq!(1, fs.width);
    assert_eq!(6, fs.offset);
    assert_eq!(AccessSpec::WriteOnly, fs.access.unwrap());

    fs = specs.pop().unwrap();

    assert_eq!("FOO_one", fs.name);
    assert_eq!("Bar one", fs.description.unwrap());
    assert_eq!(1, fs.width);
    assert_eq!(2, fs.offset);
    assert_eq!(AccessSpec::WriteOnly, fs.access.unwrap());
  }

  #[test]
  fn inherits_from_other_field() {
    let descendant_el: Element = Element::parse(
      r##"
      <field>
        <name>FOO</name>
        <bitOffset>1</bitOffset>
        <bitWidth>2</bitWidth>
      </field>
    "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_fi = Field::parse(&descendant_el).unwrap();
    let mut descendant_specs = FieldSpec::new(&descendant_fi, "", 0).unwrap();
    let mut descendant_fs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <field>
        <name>FOO2</name>
        <description>Baz</description>
        <bitOffset>3</bitOffset>
        <bitWidth>4</bitWidth>
        <access>read-only</access>
        <writeConstraint>
          <range>
            <minimum>2</minimum>
            <maximum>4</maximum>
          </range>
        </writeConstraint>
        <modifiedWriteValues>zeroToToggle</modifiedWriteValues>
      </field>
    "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_fi = Field::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = FieldSpec::new(&ancestor_fi, "", 0).unwrap();
    let ancestor_fs = ancestor_specs.pop().unwrap();

    let changed = descendant_fs.inherit_from(&ancestor_fs);

    assert!(changed);

    // Not inherited
    assert_eq!("FOO", descendant_fs.name);
    assert_eq!(2, descendant_fs.width);
    assert_eq!(1, descendant_fs.offset);
    assert_eq!(
      WriteConstraintSpec::Range(WriteConstraintRangeSpec { min: 2, max: 4 }),
      descendant_fs.write_constraint.unwrap()
    );
    assert_eq!(
      ModifiedWriteValuesSpec::ZeroToToggle,
      descendant_fs.modified_write_values.unwrap()
    );

    // Inherited
    assert_eq!("Baz", descendant_fs.description.unwrap());
    assert_eq!(AccessSpec::ReadOnly, descendant_fs.access.unwrap());
  }

  #[test]
  fn inherits_from_returns_false_when_no_changes() {
    let descendant_el: Element = Element::parse(
      r##"
      <field>
        <name>FOO</name>
        <description>BAR</description>
        <bitOffset>1</bitOffset>
        <bitWidth>2</bitWidth>
        <access>read-write</access>
      </field>
    "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_fi = Field::parse(&descendant_el).unwrap();
    let mut descendant_specs = FieldSpec::new(&descendant_fi, "", 0).unwrap();
    let mut descendant_fs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <field>
        <name>FOO2</name>
        <description>Baz</description>
        <bitOffset>3</bitOffset>
        <bitWidth>4</bitWidth>
        <access>read-only</access>
      </field>
    "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_fi = Field::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = FieldSpec::new(&ancestor_fi, "", 0).unwrap();
    let ancestor_fs = ancestor_specs.pop().unwrap();

    let changed = descendant_fs.inherit_from(&ancestor_fs);

    assert!(!changed);

    assert_eq!("FOO", descendant_fs.name);
    assert_eq!(2, descendant_fs.width);
    assert_eq!(1, descendant_fs.offset);
    assert_eq!("BAR", descendant_fs.description.unwrap());
    assert_eq!(AccessSpec::ReadWrite, descendant_fs.access.unwrap());
  }

  #[test]
  pub fn single_has_correct_path() {
    let el: Element = Element::parse(
      r##"
      <field>
        <name>FOO</name>
        <bitOffset>2</bitOffset>
        <bitWidth>1</bitWidth>
      </field>
      "##
        .as_bytes(),
    )
    .unwrap();

    let fi = Field::parse(&el).unwrap();
    let fs = FieldSpec::new(&fi, "path", 0).unwrap();

    assert_eq!("path.FOO", fs[0].path());
  }

  #[test]
  pub fn multiples_have_correct_paths() {
    let el: Element = Element::parse(
      r##"
      <field>
        <name>FOO_%s</name>
        <bitOffset>2</bitOffset>
        <bitWidth>1</bitWidth>
        <dim>3</dim>
        <dimIndex>one,two,three</dimIndex>
        <dimIncrement>0x4</dimIncrement>
      </field>
      "##
        .as_bytes(),
    )
    .unwrap();

    let fi = Field::parse(&el).unwrap();
    let fs = FieldSpec::new(&fi, "path", 0).unwrap();

    assert_eq!("path.FOO_one", fs[0].path());
    assert_eq!("path.FOO_two", fs[1].path());
    assert_eq!("path.FOO_three", fs[2].path());
  }

  #[test]
  pub fn single_has_correct_derived_from_path() {
    let el: Element = Element::parse(
      r##"
      <field derivedFrom="BAR">
        <name>FOO</name>
        <bitOffset>2</bitOffset>
        <bitWidth>1</bitWidth>
      </field>
      "##
        .as_bytes(),
    )
    .unwrap();

    let fi = Field::parse(&el).unwrap();
    let fs = FieldSpec::new(&fi, "path", 0).unwrap();

    assert_eq!("path.BAR", fs[0].derived_from_path().unwrap());
  }

  #[test]
  pub fn multiples_have_correct_derived_from_paths() {
    let el: Element = Element::parse(
      r##"
      <field derivedFrom="BAR_%s">
        <name>FOO_%s</name>
        <bitOffset>2</bitOffset>
        <bitWidth>1</bitWidth>
        <dim>3</dim>
        <dimIndex>one,two,three</dimIndex>
        <dimIncrement>0x4</dimIncrement>
      </field>
      "##
        .as_bytes(),
    )
    .unwrap();

    let fi = Field::parse(&el).unwrap();
    let fs = FieldSpec::new(&fi, "path", 0).unwrap();

    assert_eq!("path.BAR_one", fs[0].derived_from_path().unwrap());
    assert_eq!("path.BAR_two", fs[1].derived_from_path().unwrap());
    assert_eq!("path.BAR_three", fs[2].derived_from_path().unwrap());
  }

  #[test]
  pub fn propagates_default_register_properties() {
    let el: Element = Element::parse(
      r##"
      <field>
        <name>FOO</name>
        <bitOffset>2</bitOffset>
        <bitWidth>3</bitWidth>
      </field>
      "##
        .as_bytes(),
    )
    .unwrap();

    let fi = Field::parse(&el).unwrap();
    let mut fs = FieldSpec::new(&fi, "path", 0).unwrap();
    let field = &mut fs[0];

    let changed = field.propagate_default_properties(
      &Some(AccessSpec::ReadWriteOnce),
      &Some(WriteConstraintSpec::Range(WriteConstraintRangeSpec {
        min: 2,
        max: 4,
      })),
      &Some(ModifiedWriteValuesSpec::ZeroToToggle),
      &Some(u32::MAX),
      &Some(1 << 3),
    );

    assert!(changed);
    assert_eq!(AccessSpec::ReadWriteOnce, field.access.unwrap());
    assert_eq!(
      WriteConstraintSpec::Range(WriteConstraintRangeSpec { min: 2, max: 4 }),
      field.write_constraint.clone().unwrap()
    );
    assert_eq!(
      ModifiedWriteValuesSpec::ZeroToToggle,
      field.modified_write_values.clone().unwrap()
    );
    assert_eq!(0b11100, field.reset_mask.clone().unwrap());
    assert_eq!(0b10, field.reset_value.clone().unwrap());
  }

  #[test]
  pub fn propagate_default_register_properties_returns_false_when_no_changes() {
    let el: Element = Element::parse(
      r##"
      <field>
        <name>FOO</name>
        <bitOffset>2</bitOffset>
        <bitWidth>3</bitWidth>
      </field>
      "##
        .as_bytes(),
    )
    .unwrap();

    let fi = Field::parse(&el).unwrap();
    let mut fs = FieldSpec::new(&fi, "path", 0).unwrap();
    let mut field = &mut fs[0];
    field.reset_mask = Some(0b11100);
    field.reset_value = Some(0b10);

    let changed =
      field.propagate_default_properties(&None, &None, &None, &Some(u32::MAX), &Some(1 << 4));

    assert!(!changed);
    assert!(field.access.is_none());
    assert!(field.write_constraint.is_none());
    assert!(field.modified_write_values.is_none());
    assert!(field.reset_mask.is_some());
    assert!(field.reset_value.is_some());
  }
}
