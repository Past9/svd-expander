use crate::{SvdExpanderError, SvdExpanderResult};
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
  pub fn new(mwv: &ModifiedWriteValues) -> Self {
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
  pub fn new(wc: &WriteConstraint) -> Self {
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
  pub fn new(wcr: &WriteConstraintRange) -> Self {
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
  pub fn new(u: &Usage) -> Self {
    match u {
      Usage::Read => EnumeratedValueUsageSpec::Read,
      Usage::Write => EnumeratedValueUsageSpec::Write,
      Usage::ReadWrite => EnumeratedValueUsageSpec::ReadWrite,
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumeratedValueSetSpec {
  derived_from: Option<String>,
  pub name: Option<String>,
  pub usage: Option<EnumeratedValueUsageSpec>,
  pub values: Vec<EnumeratedValueSpec>,
}
impl EnumeratedValueSetSpec {
  pub fn new(ev: &EnumeratedValues) -> SvdExpanderResult<Self> {
    Ok(Self {
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
        .collect::<SvdExpanderResult<Vec<EnumeratedValueSpec>>>()?,
    })
  }
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumeratedValueSpec {
  pub name: String,
  pub description: Option<String>,
  pub value: EnumeratedValueValueSpec,
}
impl EnumeratedValueSpec {
  pub fn new(ev: &EnumeratedValue) -> SvdExpanderResult<Self> {
    Ok(Self {
      name: ev.name.clone(),
      description: ev.description.clone(),
      value: match (ev.value, ev.is_default) {
        (Some(v), _) => EnumeratedValueValueSpec::Value(v),
        (None, Some(true)) => EnumeratedValueValueSpec::Default,
        (None, None) => {
          return Err(SvdExpanderError::new(
            "Can't interpret enumerated value with no value and no is_default tag.",
          ))
        }
        (None, Some(false)) => {
          return Err(SvdExpanderError::new(
            "Can't interpret enumerated value with no value where is_default=false.",
          ))
        }
      },
    })
  }
}

#[derive(Debug, Clone, PartialEq)]
pub enum EnumeratedValueValueSpec {
  Value(u32),
  Default,
}
