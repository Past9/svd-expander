use crate::SvdExpanderResult;
use svd_parser::{
  writeconstraint::WriteConstraintRange, EnumeratedValue, EnumeratedValues, ModifiedWriteValues,
  Usage, WriteConstraint,
};

#[derive(Debug, Clone, PartialEq)]
pub enum ModifiedWriteValuesSpec {
  OneToClear,
  OneToSet,
  OneToToggle,
  ZeroToClear,
  ZeroToSet,
  ZeroToToggle,
  Clear,
  Set,
  Modify,
}
impl ModifiedWriteValuesSpec {
  pub(crate) fn new(mwv: &ModifiedWriteValues) -> Self {
    match mwv {
      ModifiedWriteValues::OneToClear => ModifiedWriteValuesSpec::OneToClear,
      ModifiedWriteValues::OneToSet => ModifiedWriteValuesSpec::OneToSet,
      ModifiedWriteValues::OneToToggle => ModifiedWriteValuesSpec::OneToToggle,

      ModifiedWriteValues::ZeroToClear => ModifiedWriteValuesSpec::ZeroToClear,
      ModifiedWriteValues::ZeroToSet => ModifiedWriteValuesSpec::ZeroToSet,
      ModifiedWriteValues::ZeroToToggle => ModifiedWriteValuesSpec::ZeroToToggle,

      ModifiedWriteValues::Clear => ModifiedWriteValuesSpec::Clear,
      ModifiedWriteValues::Set => ModifiedWriteValuesSpec::Set,
      ModifiedWriteValues::Modify => ModifiedWriteValuesSpec::Modify,
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub enum WriteConstraintSpec {
  UseEnumeratedValues,
  Range(WriteConstraintRangeSpec),
  WriteAsRead,
  Unconstrained,
}
impl WriteConstraintSpec {
  pub(crate) fn new(wc: &WriteConstraint) -> Self {
    match wc {
      WriteConstraint::WriteAsRead(true) => WriteConstraintSpec::WriteAsRead,
      WriteConstraint::UseEnumeratedValues(true) => WriteConstraintSpec::UseEnumeratedValues,
      WriteConstraint::Range(ref wcr) => {
        WriteConstraintSpec::Range(WriteConstraintRangeSpec::new(wcr))
      }
      _ => WriteConstraintSpec::Unconstrained,
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct WriteConstraintRangeSpec {
  pub min: u32,
  pub max: u32,
}
impl WriteConstraintRangeSpec {
  pub(crate) fn new(wcr: &WriteConstraintRange) -> Self {
    Self {
      min: wcr.min,
      max: wcr.max,
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub enum EnumeratedValueUsageSpec {
  Read,
  Write,
  ReadWrite,
}
impl EnumeratedValueUsageSpec {
  pub(crate) fn new(u: &Usage) -> Self {
    match u {
      Usage::Read => EnumeratedValueUsageSpec::Read,
      Usage::Write => EnumeratedValueUsageSpec::Write,
      Usage::ReadWrite => EnumeratedValueUsageSpec::ReadWrite,
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumeratedValueSetSpec {
  preceding_path: String,
  derived_from: Option<String>,
  pub name: Option<String>,
  pub usage: Option<EnumeratedValueUsageSpec>,
  pub values: Vec<EnumeratedValueSpec>,
}
impl EnumeratedValueSetSpec {
  pub(crate) fn new(ev: &EnumeratedValues, preceding_path: &str) -> SvdExpanderResult<Self> {
    Ok(Self {
      preceding_path: preceding_path.to_owned(),
      derived_from: ev.derived_from.clone(),
      name: ev.name.clone(),
      usage: match ev.usage {
        Some(ref u) => Some(EnumeratedValueUsageSpec::new(u)),
        None => None,
      },
      values: ev
        .values
        .iter()
        .map(|v| EnumeratedValueSpec::new(&v))
        .collect(),
    })
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

  pub fn path(&self) -> Option<String> {
    match self.name {
      Some(ref n) => Some(format!("{}.{}", self.preceding_path, n)),
      None => None,
    }
  }

  pub(crate) fn clone_with_preceding_path(&self, preceding_path: &str) -> Self {
    Self {
      preceding_path: preceding_path.to_owned(),
      derived_from: None,
      name: self.name.clone(),
      usage: self.usage.clone(),
      values: self.values.clone(),
    }
  }

  pub(crate) fn inherit_from(&mut self, ss: &EnumeratedValueSetSpec) -> bool {
    let mut changed = false;

    if self.usage.is_none() && ss.usage.is_some() {
      self.usage = ss.usage.clone();
      changed = true;
    }

    for ancestor in ss.values.iter() {
      if let Some(ref mut descendant) = self.values.iter_mut().find(|f| f.name == ancestor.name) {
        if descendant.inherit_from(ancestor) {
          changed = true;
        }
      } else {
        self.values.push(ancestor.clone());
        changed = true;
      }
    }

    changed
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumeratedValueSpec {
  pub name: String,
  pub description: Option<String>,
  pub value: Option<EnumeratedValueValueSpec>,
}
impl EnumeratedValueSpec {
  pub(crate) fn new(ev: &EnumeratedValue) -> Self {
    Self {
      name: ev.name.clone(),
      description: ev.description.clone(),
      value: match (ev.value, ev.is_default) {
        (Some(v), _) => Some(EnumeratedValueValueSpec::Value(v)),
        (None, Some(true)) => Some(EnumeratedValueValueSpec::Default),
        (None, None) => None,
        (None, Some(false)) => None,
      },
    }
  }

  pub(crate) fn inherit_from(&mut self, vs: &EnumeratedValueSpec) -> bool {
    let mut changed = false;

    if self.description.is_none() && vs.description.is_some() {
      self.description = vs.description.clone();
      changed = true;
    }

    if self.value.is_none() && vs.value.is_some() {
      self.value = vs.value.clone();
      changed = true;
    }

    changed
  }
}

#[derive(Debug, Clone, PartialEq)]
pub enum EnumeratedValueValueSpec {
  Value(u32),
  Default,
}
