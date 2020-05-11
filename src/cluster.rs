use svd_parser::{Cluster, ClusterInfo, RegisterCluster};

use super::register::RegisterSpec;
use super::{AccessSpec, FieldSpec};
use crate::error::{Result, SvdExpanderError};

#[derive(Debug, Clone, PartialEq)]
pub struct ClusterSpec {
  preceding_path: String,
  pub derived_from: Option<String>,
  pub name: String,
  pub description: Option<String>,
  pub address_offset: u32,
  pub default_register_size: Option<u32>,
  pub default_register_reset_value: Option<u32>,
  pub default_register_reset_mask: Option<u32>,
  pub default_register_access: Option<AccessSpec>,
  pub registers: Vec<RegisterSpec>,
  pub clusters: Vec<ClusterSpec>,
}
impl ClusterSpec {
  pub fn new(c: &Cluster, preceding_path: &str) -> Result<Vec<Self>> {
    let specs: Vec<Self> = match c {
      Cluster::Single(ref ci) => vec![Self::from_cluster_info(ci, preceding_path)],
      Cluster::Array(ref ci, ref d) => {
        let dim_indices = if let Some(ref di) = d.dim_index {
          if d.dim != di.len() as u32 {
            return Err(SvdExpanderError::new(&format!(
              "Cluster {}: 'dim' element must have the same value as the length of 'dimIndex'",
              &c.name
            )));
          }
          di
        } else {
          return Err(SvdExpanderError::new(&format!(
            "Cluster {}: 'dimIndex' element is required",
            &c.name
          )));
        };

        let prototype = Self::from_cluster_info(ci, preceding_path);
        let mut cluster_specs = Vec::with_capacity(d.dim as usize);

        for (n, dim_index) in dim_indices.iter().enumerate() {
          let mut spec = prototype.clone();
          spec.interpolate_array_params(
            dim_index.clone(),
            prototype.address_offset + n as u32 * d.dim_increment,
          );
          cluster_specs.push(spec);
        }

        cluster_specs
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
      address_offset: self.address_offset,
      default_register_size: self.default_register_size,
      default_register_reset_value: self.default_register_reset_value,
      default_register_reset_mask: self.default_register_reset_mask,
      default_register_access: self.default_register_access,
      registers: self
        .registers
        .iter()
        .map(|r| r.clone_with_preceding_path(preceding_path))
        .collect(),
      clusters: self
        .clusters
        .iter()
        .map(|c| c.clone_with_preceding_path(preceding_path))
        .collect(),
    }
  }

  pub fn mutate_clusters<F>(&mut self, f: F) -> Result<bool>
  where
    F: Fn(&mut ClusterSpec) -> Result<bool>,
    F: Copy,
  {
    let mut changed = false;

    for child in &mut self.clusters.iter_mut() {
      if child.mutate_clusters(f)? {
        changed = true;
      }
    }

    if f(self)? {
      changed = true;
    }

    Ok(changed)
  }

  pub fn iter_clusters<'a>(&'a self) -> Box<dyn Iterator<Item = &ClusterSpec> + 'a> {
    Box::new(
      self
        .clusters
        .iter()
        .flat_map(|c| c.iter_clusters())
        .chain(vec![self]),
    )
  }

  pub fn mutate_registers<F>(&mut self, f: F) -> Result<bool>
  where
    F: Fn(&mut RegisterSpec) -> Result<bool>,
    F: Copy,
  {
    let mut changed = false;

    for child in &mut self.clusters.iter_mut() {
      if child.mutate_registers(f)? {
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

  pub fn iter_registers<'a>(&'a self) -> Box<dyn Iterator<Item = &RegisterSpec> + 'a> {
    Box::new(
      self
        .clusters
        .iter()
        .flat_map(|c| c.iter_registers())
        .chain(self.registers.iter()),
    )
  }

  pub fn iter_fields<'a>(&'a self) -> Box<dyn Iterator<Item = &FieldSpec> + 'a> {
    Box::new(self.iter_registers().flat_map(|r| r.fields.iter()))
  }

  pub fn mutate_fields<F>(&mut self, f: F) -> Result<bool>
  where
    F: Fn(&mut FieldSpec) -> Result<bool>,
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

  fn from_cluster_info(ci: &ClusterInfo, preceding_path: &str) -> Self {
    let mut cluster = Self {
      preceding_path: preceding_path.to_owned(),
      derived_from: ci.derived_from.clone(),
      name: ci.name.clone(),
      description: ci.description.clone(),
      address_offset: ci.address_offset,
      default_register_size: ci.default_register_properties.size.clone(),
      default_register_reset_value: ci.default_register_properties.reset_value.clone(),
      default_register_reset_mask: ci.default_register_properties.reset_mask.clone(),
      default_register_access: match ci.default_register_properties.access {
        Some(ref a) => Some(AccessSpec::new(a)),
        None => None,
      },
      registers: Vec::with_capacity(0),
      clusters: Vec::with_capacity(0),
    };

    cluster.registers = ci
      .children
      .iter()
      .filter_map(|child| match child {
        RegisterCluster::Register(ref r) => Some(RegisterSpec::new(r, &cluster.path())),
        RegisterCluster::Cluster(_) => None,
      })
      .flatten()
      .flatten()
      .collect();

    cluster.clusters = ci
      .children
      .iter()
      .filter_map(|child| match child {
        RegisterCluster::Cluster(ref c) => Some(ClusterSpec::new(c, &cluster.path())),
        RegisterCluster::Register(_) => None,
      })
      .flatten()
      .flatten()
      .collect();

    cluster
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
  }

  pub fn inherit_from(&mut self, cs: &ClusterSpec) -> bool {
    let mut changed = false;

    if self.description.is_none() && cs.description.is_some() {
      self.description = cs.description.clone();
      changed = true;
    }

    if self.default_register_size.is_none() && cs.default_register_size.is_some() {
      self.default_register_size = cs.default_register_size;
      changed = true;
    }

    if self.default_register_access.is_none() && cs.default_register_access.is_some() {
      self.default_register_access = cs.default_register_access;
      changed = true;
    }

    if self.default_register_reset_value.is_none() && cs.default_register_reset_value.is_some() {
      self.default_register_reset_value = cs.default_register_reset_value;
      changed = true;
    }

    if self.default_register_reset_mask.is_none() && cs.default_register_reset_mask.is_some() {
      self.default_register_reset_mask = cs.default_register_reset_mask;
      changed = true;
    }

    for ancestor in cs.registers.iter() {
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

    for ancestor in cs.clusters.iter() {
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

  pub fn propagate_default_register_properties(
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

  use super::ClusterSpec;
  use crate::{AccessSpec, FieldSpec, RegisterSpec};
  use std::cell::RefCell;
  use svd_parser::{parse::Parse, Cluster};
  use xmltree::Element;

  #[test]
  fn can_create_single_from_xml() {
    let el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO</name>
        <description>Bar</description>
        <addressOffset>3000</addressOffset>
        <access>write-only</access>
        <resetValue>1234</resetValue>
        <resetMask>4321</resetMask>
        <size>16</size>
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
      </cluster>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ci = Cluster::parse(&el).unwrap();

    let mut specs = ClusterSpec::new(&ci, "").unwrap();

    assert_eq!(1, specs.len());

    let cs = specs.pop().unwrap();

    assert_eq!("FOO", cs.name);
    assert_eq!("Bar", cs.description.unwrap());
    assert_eq!(3000, cs.address_offset);
    assert_eq!(AccessSpec::WriteOnly, cs.default_register_access.unwrap());
    assert_eq!(1234, cs.default_register_reset_value.unwrap());
    assert_eq!(4321, cs.default_register_reset_mask.unwrap());
    assert_eq!(16, cs.default_register_size.unwrap());

    assert_eq!(2, cs.registers.len());
    assert_eq!("R1", cs.registers[0].name);
    assert_eq!("R2", cs.registers[1].name);

    assert_eq!(1, cs.clusters.len());
    assert_eq!("C1", cs.clusters[0].name);
  }

  #[test]
  fn can_create_multiple_from_xml() {
    let el: Element = Element::parse(
      r##"
      <cluster>
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
      </cluster>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ci = Cluster::parse(&el).unwrap();

    let mut specs = ClusterSpec::new(&ci, "").unwrap();

    assert_eq!(3, specs.len());

    let mut cs = specs.pop().unwrap();

    assert_eq!("FOO_three", cs.name);
    assert_eq!("Bar three", cs.description.unwrap());
    assert_eq!(3064, cs.address_offset);
    assert_eq!(AccessSpec::WriteOnly, cs.default_register_access.unwrap());
    assert_eq!(1234, cs.default_register_reset_value.unwrap());
    assert_eq!(4321, cs.default_register_reset_mask.unwrap());
    assert_eq!(16, cs.default_register_size.unwrap());

    assert_eq!(2, cs.registers.len());
    assert_eq!("R1", cs.registers[0].name);
    assert_eq!("R2", cs.registers[1].name);

    assert_eq!(1, cs.clusters.len());
    assert_eq!("C1", cs.clusters[0].name);

    cs = specs.pop().unwrap();

    assert_eq!("FOO_two", cs.name);
    assert_eq!("Bar two", cs.description.unwrap());
    assert_eq!(3032, cs.address_offset);
    assert_eq!(AccessSpec::WriteOnly, cs.default_register_access.unwrap());
    assert_eq!(1234, cs.default_register_reset_value.unwrap());
    assert_eq!(4321, cs.default_register_reset_mask.unwrap());
    assert_eq!(16, cs.default_register_size.unwrap());

    assert_eq!(2, cs.registers.len());
    assert_eq!("R1", cs.registers[0].name);
    assert_eq!("R2", cs.registers[1].name);

    assert_eq!(1, cs.clusters.len());
    assert_eq!("C1", cs.clusters[0].name);

    cs = specs.pop().unwrap();

    assert_eq!("FOO_one", cs.name);
    assert_eq!("Bar one", cs.description.unwrap());
    assert_eq!(3000, cs.address_offset);
    assert_eq!(AccessSpec::WriteOnly, cs.default_register_access.unwrap());
    assert_eq!(1234, cs.default_register_reset_value.unwrap());
    assert_eq!(4321, cs.default_register_reset_mask.unwrap());
    assert_eq!(16, cs.default_register_size.unwrap());

    assert_eq!(2, cs.registers.len());
    assert_eq!("R1", cs.registers[0].name);
    assert_eq!("R2", cs.registers[1].name);

    assert_eq!(1, cs.clusters.len());
    assert_eq!("C1", cs.clusters[0].name);
  }

  #[test]
  fn inherits_from_other_cluster() {
    let descendant_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO</name>
        <addressOffset>1000</addressOffset>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_ci = Cluster::parse(&descendant_el).unwrap();
    let mut descendant_specs = ClusterSpec::new(&descendant_ci, "").unwrap();
    let mut descendant_cs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO2</name>
        <description>Bar</description>
        <addressOffset>3000</addressOffset>
        <access>write-only</access>
        <resetValue>1234</resetValue>
        <resetMask>4321</resetMask>
        <size>16</size>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_ci = Cluster::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = ClusterSpec::new(&ancestor_ci, "").unwrap();
    let ancestor_cs = ancestor_specs.pop().unwrap();

    let changed = descendant_cs.inherit_from(&ancestor_cs);

    assert!(changed);

    // Not inherited
    assert_eq!("FOO", descendant_cs.name);
    assert_eq!(1000, descendant_cs.address_offset);

    // Inherited
    assert_eq!("Bar", descendant_cs.description.unwrap());
    assert_eq!(
      AccessSpec::WriteOnly,
      descendant_cs.default_register_access.unwrap()
    );
    assert_eq!(1234, descendant_cs.default_register_reset_value.unwrap());
    assert_eq!(4321, descendant_cs.default_register_reset_mask.unwrap());
    assert_eq!(16, descendant_cs.default_register_size.unwrap());
  }

  #[test]
  fn inherits_from_returns_false_when_no_changes() {
    let descendant_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO</name>
        <description>Baz</description>
        <addressOffset>1000</addressOffset>
        <access>read-only</access>
        <resetValue>2345</resetValue>
        <resetMask>6543</resetMask>
        <size>32</size>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_ci = Cluster::parse(&descendant_el).unwrap();
    let mut descendant_specs = ClusterSpec::new(&descendant_ci, "").unwrap();
    let mut descendant_cs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO2</name>
        <description>Bar</description>
        <addressOffset>3000</addressOffset>
        <access>write-only</access>
        <resetValue>1234</resetValue>
        <resetMask>4321</resetMask>
        <size>16</size>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_ci = Cluster::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = ClusterSpec::new(&ancestor_ci, "").unwrap();
    let ancestor_cs = ancestor_specs.pop().unwrap();

    let changed = descendant_cs.inherit_from(&ancestor_cs);

    assert!(!changed);

    assert_eq!("FOO", descendant_cs.name);
    assert_eq!("Baz", descendant_cs.description.unwrap());
    assert_eq!(1000, descendant_cs.address_offset);
    assert_eq!(
      AccessSpec::ReadOnly,
      descendant_cs.default_register_access.unwrap()
    );
    assert_eq!(2345, descendant_cs.default_register_reset_value.unwrap());
    assert_eq!(6543, descendant_cs.default_register_reset_mask.unwrap());
    assert_eq!(32, descendant_cs.default_register_size.unwrap());
  }

  #[test]
  fn inherits_from_returns_true_for_overridden_inherited_cluster() {
    let descendant_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO</name>
        <addressOffset>1000</addressOffset>
        <cluster>
          <name>FOO_sub</name>
          <addressOffset>3100</addressOffset>
        </cluster>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_ci = Cluster::parse(&descendant_el).unwrap();
    let mut descendant_specs = ClusterSpec::new(&descendant_ci, "").unwrap();
    let mut descendant_cs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO2</name>
        <addressOffset>3000</addressOffset>
        <cluster>
          <name>FOO_sub</name>
          <addressOffset>3200</addressOffset>
          <description>BAZ</description>
        </cluster>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_ci = Cluster::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = ClusterSpec::new(&ancestor_ci, "").unwrap();
    let ancestor_cs = ancestor_specs.pop().unwrap();

    let changed = descendant_cs.inherit_from(&ancestor_cs);

    assert!(changed);

    assert_eq!("FOO", descendant_cs.name);
    assert_eq!(1000, descendant_cs.address_offset);

    assert_eq!(1, descendant_cs.clusters.len());

    assert_eq!("FOO_sub", descendant_cs.clusters[0].name);
    assert_eq!(3100, descendant_cs.clusters[0].address_offset);
    assert_eq!(
      "BAZ",
      descendant_cs.clusters[0].description.clone().unwrap()
    );
  }

  #[test]
  fn inherits_from_returns_true_for_added_inherited_cluster() {
    let descendant_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO</name>
        <addressOffset>1000</addressOffset>
        <cluster>
          <name>FOO_sub</name>
          <addressOffset>3100</addressOffset>
        </cluster>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_ci = Cluster::parse(&descendant_el).unwrap();
    let mut descendant_specs = ClusterSpec::new(&descendant_ci, "").unwrap();
    let mut descendant_cs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO2</name>
        <addressOffset>3000</addressOffset>
        <cluster>
          <name>FOO_sub2</name>
          <addressOffset>3200</addressOffset>
          <description>BAZ</description>
        </cluster>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_ci = Cluster::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = ClusterSpec::new(&ancestor_ci, "").unwrap();
    let ancestor_cs = ancestor_specs.pop().unwrap();

    let changed = descendant_cs.inherit_from(&ancestor_cs);

    assert!(changed);

    assert_eq!("FOO", descendant_cs.name);
    assert_eq!(1000, descendant_cs.address_offset);

    assert_eq!(2, descendant_cs.clusters.len());

    assert_eq!("FOO_sub", descendant_cs.clusters[0].name);
    assert_eq!(3100, descendant_cs.clusters[0].address_offset);
    assert!(descendant_cs.clusters[0].description.is_none());

    assert_eq!("FOO_sub2", descendant_cs.clusters[1].name);
    assert_eq!(3200, descendant_cs.clusters[1].address_offset);
    assert_eq!(
      "BAZ",
      descendant_cs.clusters[1].description.clone().unwrap()
    );
  }

  #[test]
  fn inherits_from_returns_true_for_overridden_inherited_register() {
    let descendant_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO</name>
        <addressOffset>1000</addressOffset>
        <register>
          <name>FOO_sub</name>
          <addressOffset>3100</addressOffset>
        </register>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_ci = Cluster::parse(&descendant_el).unwrap();
    let mut descendant_specs = ClusterSpec::new(&descendant_ci, "").unwrap();
    let mut descendant_cs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO2</name>
        <addressOffset>3000</addressOffset>
        <register>
          <name>FOO_sub</name>
          <addressOffset>3200</addressOffset>
          <description>BAZ</description>
        </register>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_ci = Cluster::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = ClusterSpec::new(&ancestor_ci, "").unwrap();
    let ancestor_cs = ancestor_specs.pop().unwrap();

    let changed = descendant_cs.inherit_from(&ancestor_cs);

    assert!(changed);

    assert_eq!("FOO", descendant_cs.name);
    assert_eq!(1000, descendant_cs.address_offset);

    assert_eq!(1, descendant_cs.registers.len());

    assert_eq!("FOO_sub", descendant_cs.registers[0].name);
    assert_eq!(3100, descendant_cs.registers[0].address_offset);
    assert_eq!(
      "BAZ",
      descendant_cs.registers[0].description.clone().unwrap()
    );
  }

  #[test]
  fn inherits_from_returns_true_for_added_inherited_register() {
    let descendant_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO</name>
        <addressOffset>1000</addressOffset>
        <register>
          <name>FOO_sub</name>
          <addressOffset>3100</addressOffset>
        </register>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let descendant_ci = Cluster::parse(&descendant_el).unwrap();
    let mut descendant_specs = ClusterSpec::new(&descendant_ci, "").unwrap();
    let mut descendant_cs = descendant_specs.pop().unwrap();

    let ancestor_el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO2</name>
        <addressOffset>3000</addressOffset>
        <register>
          <name>FOO_sub2</name>
          <addressOffset>3200</addressOffset>
          <description>BAZ</description>
        </register>
      </cluster>
    "##
        .as_bytes(),
    )
    .unwrap();

    let ancestor_ci = Cluster::parse(&ancestor_el).unwrap();
    let mut ancestor_specs = ClusterSpec::new(&ancestor_ci, "").unwrap();
    let ancestor_cs = ancestor_specs.pop().unwrap();

    let changed = descendant_cs.inherit_from(&ancestor_cs);

    assert!(changed);

    assert_eq!("FOO", descendant_cs.name);
    assert_eq!(1000, descendant_cs.address_offset);

    assert_eq!(2, descendant_cs.registers.len());

    assert_eq!("FOO_sub", descendant_cs.registers[0].name);
    assert_eq!(3100, descendant_cs.registers[0].address_offset);
    assert!(descendant_cs.registers[0].description.is_none());

    assert_eq!("FOO_sub2", descendant_cs.registers[1].name);
    assert_eq!(3200, descendant_cs.registers[1].address_offset);
    assert_eq!(
      "BAZ",
      descendant_cs.registers[1].description.clone().unwrap()
    );
  }

  #[test]
  fn single_has_correct_path() {
    let el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO</name>
        <addressOffset>3000</addressOffset>
      </cluster>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Cluster::parse(&el).unwrap();
    let rs = ClusterSpec::new(&ri, "path").unwrap();

    assert_eq!("path.FOO", rs[0].path());
  }

  #[test]
  fn multiples_have_correct_paths() {
    let el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO_%s</name>
        <addressOffset>3000</addressOffset>
        <dim>3</dim>
        <dimIndex>one,two,three</dimIndex>
        <dimIncrement>0x4</dimIncrement>
      </cluster>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Cluster::parse(&el).unwrap();
    let rs = ClusterSpec::new(&ri, "path").unwrap();

    assert_eq!("path.FOO_one", rs[0].path());
    assert_eq!("path.FOO_two", rs[1].path());
    assert_eq!("path.FOO_three", rs[2].path());
  }

  #[test]
  fn single_has_correct_derived_from_path() {
    let el: Element = Element::parse(
      r##"
      <cluster derivedFrom="BAR">
        <name>FOO</name>
        <addressOffset>3000</addressOffset>
      </cluster>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Cluster::parse(&el).unwrap();
    let rs = ClusterSpec::new(&ri, "path").unwrap();

    assert_eq!("path.BAR", rs[0].derived_from_path().unwrap());
  }

  #[test]
  fn multiples_have_correct_derived_from_paths() {
    let el: Element = Element::parse(
      r##"
      <cluster derivedFrom="BAR_%s">
        <name>FOO_%s</name>
        <addressOffset>3000</addressOffset>
        <dim>3</dim>
        <dimIndex>one,two,three</dimIndex>
        <dimIncrement>0x4</dimIncrement>
      </cluster>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ri = Cluster::parse(&el).unwrap();
    let rs = ClusterSpec::new(&ri, "path").unwrap();

    assert_eq!("path.BAR_one", rs[0].derived_from_path().unwrap());
    assert_eq!("path.BAR_two", rs[1].derived_from_path().unwrap());
    assert_eq!("path.BAR_three", rs[2].derived_from_path().unwrap());
  }

  #[test]
  fn recursively_iterates_clusters() {
    let el: Element = Element::parse(
      r##"
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
      "##
        .as_bytes(),
    )
    .unwrap();

    let ci = Cluster::parse(&el).unwrap();
    let cs = ClusterSpec::new(&ci, "path").unwrap();

    assert_eq!(1, cs.len());

    let top = &cs[0];

    let all_clusters: Vec<&ClusterSpec> = top.iter_clusters().collect();

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
      <cluster>
        <name>FOO5</name>
        <addressOffset>5000</addressOffset>
        <cluster>
          <name>FOO1</name>
          <addressOffset>1000</addressOffset>
        </cluster>
        <cluster>
          <name>FOO4</name>
          <addressOffset>4000</addressOffset>
          <cluster>
            <name>FOO2</name>
            <addressOffset>2000</addressOffset>
          </cluster>
          <cluster>
            <name>FOO3</name>
            <addressOffset>3000</addressOffset>
          </cluster>
        </cluster>
      </cluster>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ci = Cluster::parse(&el).unwrap();
    let mut cs = ClusterSpec::new(&ci, "path").unwrap();

    assert_eq!(1, cs.len());

    let top = &mut cs[0];
    let count = RefCell::new(0);

    top
      .mutate_clusters(|c| {
        c.name = format!("{} {}", c.name, count.borrow());
        let current = (*count.borrow()).clone();
        *count.borrow_mut() = current + 1;
        Ok(false)
      })
      .unwrap();

    let all_clusters: Vec<&ClusterSpec> = top.iter_clusters().collect();

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
      "##
        .as_bytes(),
    )
    .unwrap();

    let ci = Cluster::parse(&el).unwrap();
    let cs = ClusterSpec::new(&ci, "path").unwrap();

    assert_eq!(1, cs.len());

    let top = &cs[0];

    let all_clusters: Vec<&RegisterSpec> = top.iter_registers().collect();

    assert_eq!("FOO1", all_clusters[0].name);
    assert_eq!("FOO2", all_clusters[1].name);
    assert_eq!("FOO3", all_clusters[2].name);
    assert_eq!("FOO4", all_clusters[3].name);
    assert_eq!("FOO5", all_clusters[4].name);
  }

  #[test]
  fn recursively_mutates_registers() {
    let el: Element = Element::parse(
      r##"
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
      "##
        .as_bytes(),
    )
    .unwrap();

    let ci = Cluster::parse(&el).unwrap();
    let mut cs = ClusterSpec::new(&ci, "path").unwrap();

    assert_eq!(1, cs.len());

    let top = &mut cs[0];
    let count = RefCell::new(0);

    top
      .mutate_registers(|r| {
        r.name = format!("{} {}", r.name, count.borrow());
        let current = (*count.borrow()).clone();
        *count.borrow_mut() = current + 1;
        Ok(false)
      })
      .unwrap();

    let all_registers: Vec<&RegisterSpec> = top.iter_registers().collect();

    assert_eq!("FOO1 0", all_registers[0].name);
    assert_eq!("FOO2 1", all_registers[1].name);
    assert_eq!("FOO3 2", all_registers[2].name);
    assert_eq!("FOO4 3", all_registers[3].name);
    assert_eq!("FOO5 4", all_registers[4].name);
  }

  #[test]
  fn recursively_mutates_fields() {
    let el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO5</name>
        <addressOffset>3000</addressOffset>
        <register>
          <name>FOO5</name>
          <addressOffset>3000</addressOffset>
          <fields>
            <field>
              <name>FOO5</name>
              <bitOffset>1</bitOffset>
              <bitWidth>1</bitWidth>
            </field>
          </fields>
        </register>
        <cluster>
          <name>FOO1</name>
          <addressOffset>3000</addressOffset>
          <register>
            <name>FOO1</name>
            <addressOffset>3000</addressOffset>
            <fields>
              <field>
                <name>FOO1</name>
                <bitOffset>1</bitOffset>
                <bitWidth>1</bitWidth>
              </field>
            </fields>
          </register>
        </cluster>
        <cluster>
          <name>FOO4</name>
          <addressOffset>3000</addressOffset>
          <register>
            <name>FOO4</name>
            <addressOffset>3000</addressOffset>
            <fields>
              <field>
                <name>FOO4</name>
                <bitOffset>1</bitOffset>
                <bitWidth>1</bitWidth>
              </field>
            </fields>
          </register>
          <cluster>
            <name>FOO2</name>
            <addressOffset>3000</addressOffset>
            <register>
              <name>FOO2</name>
              <addressOffset>3000</addressOffset>
              <fields>
                <field>
                  <name>FOO2</name>
                  <bitOffset>1</bitOffset>
                  <bitWidth>1</bitWidth>
                </field>
              </fields>
            </register>
          </cluster>
          <cluster>
            <name>FOO3</name>
            <addressOffset>3000</addressOffset>
            <register>
              <name>FOO3</name>
              <addressOffset>3000</addressOffset>
              <fields>
                <field>
                  <name>FOO3</name>
                  <bitOffset>1</bitOffset>
                  <bitWidth>1</bitWidth>
                </field>
              </fields>
            </register>
          </cluster>
        </cluster>
      </cluster>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ci = Cluster::parse(&el).unwrap();
    let mut cs = ClusterSpec::new(&ci, "path").unwrap();

    assert_eq!(1, cs.len());

    let top = &mut cs[0];
    let count = RefCell::new(0);

    top
      .mutate_fields(|f| {
        f.name = format!("{} {}", f.name, count.borrow());
        let current = (*count.borrow()).clone();
        *count.borrow_mut() = current + 1;
        Ok(false)
      })
      .unwrap();

    let all_fields: Vec<&FieldSpec> = top.iter_fields().collect();

    assert_eq!("FOO1 0", all_fields[0].name);
    assert_eq!("FOO2 1", all_fields[1].name);
    assert_eq!("FOO3 2", all_fields[2].name);
    assert_eq!("FOO4 3", all_fields[3].name);
    assert_eq!("FOO5 4", all_fields[4].name);
  }

  #[test]
  pub fn propagates_default_register_properties() {
    let el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO</name>
        <addressOffset>5000</addressOffset>
      </cluster>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ci = Cluster::parse(&el).unwrap();
    let mut cs = ClusterSpec::new(&ci, "path").unwrap();
    let cluster = &mut cs[0];

    let changed = cluster.propagate_default_register_properties(
      Some(1),
      Some(2),
      Some(3),
      Some(AccessSpec::ReadWriteOnce),
    );

    assert!(changed);
    assert_eq!(1, cluster.default_register_size.unwrap());
    assert_eq!(2, cluster.default_register_reset_value.unwrap());
    assert_eq!(3, cluster.default_register_reset_mask.unwrap());
    assert_eq!(
      AccessSpec::ReadWriteOnce,
      cluster.default_register_access.unwrap()
    );
  }

  #[test]
  pub fn propagate_default_register_properties_returns_false_when_no_changes() {
    let el: Element = Element::parse(
      r##"
      <cluster>
        <name>FOO</name>
        <addressOffset>5000</addressOffset>
      </cluster>
      "##
        .as_bytes(),
    )
    .unwrap();

    let ci = Cluster::parse(&el).unwrap();
    let mut cs = ClusterSpec::new(&ci, "path").unwrap();
    let cluster = &mut cs[0];

    let changed = cluster.propagate_default_register_properties(None, None, None, None);

    assert!(!changed);
    assert!(cluster.default_register_access.is_none());
    assert!(cluster.default_register_reset_value.is_none());
    assert!(cluster.default_register_reset_mask.is_none());
    assert!(cluster.default_register_size.is_none());
  }
}
