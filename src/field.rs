use svd_parser::{Field, FieldInfo};

use super::AccessSpec;
use crate::error::{Result, SvdExpanderError};

#[derive(Debug, Clone, PartialEq)]
pub struct FieldSpec {
  preceding_path: String,
  pub derived_from: Option<String>,
  pub name: String,
  pub description: Option<String>,
  pub offset: u32,
  pub width: u32,
  pub access: Option<AccessSpec>,
}
impl FieldSpec {
  pub fn new(f: &Field, preceding_path: &str) -> Result<Vec<Self>> {
    let specs: Vec<Self> = match f {
      Field::Single(ref fi) => vec![Self::from_field_info(fi, preceding_path)],
      Field::Array(ref fi, ref d) => {
        let dim_indices = if let Some(ref di) = d.dim_index {
          if d.dim != di.len() as u32 {
            return Err(SvdExpanderError::new(&format!(
              "Field {}: 'dim' element must have the same value as the length of 'dimIndex'",
              &f.name
            )));
          }
          di
        } else {
          return Err(SvdExpanderError::new(&format!(
            "Field {}: 'dimIndex' element is required",
            &f.name
          )));
        };

        let prototype = Self::from_field_info(fi, preceding_path);
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

  pub fn clone_with_preceding_path(&self, preceding_path: &str) -> Self {
    Self {
      preceding_path: preceding_path.to_owned(),
      derived_from: None,
      name: self.name.clone(),
      description: self.description.clone(),
      offset: self.offset,
      width: self.width,
      access: self.access,
    }
  }

  pub fn derived_from_path(&self) -> Option<String> {
    match self.derived_from {
      Some(ref df) => match df.contains(".") {
        true => Some(df.clone()),
        false => Some(format!("{}.{}", self.preceding_path, df)),
      },
      None => None,
    }
  }

  pub fn path(&self) -> String {
    format!("{}.{}", self.preceding_path, self.name)
  }

  fn from_field_info(fi: &FieldInfo, preceding_path: &str) -> Self {
    Self {
      preceding_path: preceding_path.to_owned(),
      derived_from: fi.derived_from.clone(),
      name: fi.name.clone(),
      description: fi.description.clone(),
      offset: fi.bit_range.offset,
      width: fi.bit_range.width,
      access: match fi.access {
        Some(ref a) => Some(AccessSpec::new(a)),
        None => None,
      },
    }
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

  pub fn inherit_from(&mut self, fs: &FieldSpec) -> bool {
    let mut changed = false;

    if self.description.is_none() && fs.description.is_some() {
      self.description = fs.description.clone();
      changed = true;
    }

    if self.access.is_none() && fs.access.is_some() {
      self.access = fs.access;
      changed = true
    }

    changed
  }

  pub fn propagate_default_register_properties(&mut self, access: Option<AccessSpec>) -> bool {
    let mut changed = false;

    if self.access.is_none() && access.is_some() {
      self.access = access;
      changed = true;
    }

    changed
  }
}

#[cfg(test)]
mod tests {
  use super::{AccessSpec, FieldSpec};
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
      </field>
      "##
        .as_bytes(),
    )
    .unwrap();

    let fi = Field::parse(&el).unwrap();

    let mut specs = FieldSpec::new(&fi, "").unwrap();

    assert_eq!(1, specs.len());

    let fs = specs.pop().unwrap();

    assert_eq!("FOO", fs.name);
    assert_eq!("Bar", fs.description.unwrap());
    assert_eq!(1, fs.width);
    assert_eq!(2, fs.offset);
    assert_eq!(AccessSpec::WriteOnly, fs.access.unwrap());
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

    let mut specs = FieldSpec::new(&fi, "").unwrap();

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
    let mut descendant_specs = FieldSpec::new(&descendant_fi, "").unwrap();
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
    let mut ancestor_specs = FieldSpec::new(&ancestor_fi, "").unwrap();
    let ancestor_fs = ancestor_specs.pop().unwrap();

    let changed = descendant_fs.inherit_from(&ancestor_fs);

    assert!(changed);

    // Not inherited
    assert_eq!("FOO", descendant_fs.name);
    assert_eq!(2, descendant_fs.width);
    assert_eq!(1, descendant_fs.offset);

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
    let mut descendant_specs = FieldSpec::new(&descendant_fi, "").unwrap();
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
    let mut ancestor_specs = FieldSpec::new(&ancestor_fi, "").unwrap();
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
    let fs = FieldSpec::new(&fi, "path").unwrap();

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
    let fs = FieldSpec::new(&fi, "path").unwrap();

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
    let fs = FieldSpec::new(&fi, "path").unwrap();

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
    let fs = FieldSpec::new(&fi, "path").unwrap();

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
        <bitWidth>1</bitWidth>
      </field>
      "##
        .as_bytes(),
    )
    .unwrap();

    let fi = Field::parse(&el).unwrap();
    let mut fs = FieldSpec::new(&fi, "path").unwrap();
    let field = &mut fs[0];

    let changed = field.propagate_default_register_properties(Some(AccessSpec::ReadWriteOnce));

    assert!(changed);
    assert_eq!(AccessSpec::ReadWriteOnce, field.access.unwrap());
  }

  #[test]
  pub fn propagate_default_register_properties_returns_false_when_no_changes() {
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
    let mut fs = FieldSpec::new(&fi, "path").unwrap();
    let field = &mut fs[0];

    let changed = field.propagate_default_register_properties(None);

    assert!(!changed);
    assert!(field.access.is_none());
  }
}
