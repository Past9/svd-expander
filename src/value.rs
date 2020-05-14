use crate::{SvdExpanderError, SvdExpanderResult};
use svd_parser::{
  writeconstraint::WriteConstraintRange, EnumeratedValue, EnumeratedValues, ModifiedWriteValues,
  Usage, WriteConstraint,
};

/// Describes the manipulation of data written to a field. If not specified, the values written to
/// the field is the value stored in the field.
#[derive(Debug, Clone, PartialEq)]
pub enum ModifiedWriteValuesSpec {
  /// Write data bit of one shall clear (set to zero) the corresponding bit in the field.
  OneToClear,

  /// Write data bit of one shall set (set to one) the corresponding bit in the field.
  OneToSet,

  /// Write data bit of one shall toggle (invert) the corresponding bit in the field.
  OneToToggle,

  /// Write data bit of zero shall clear (set to zero) the corresponding bit in the field.
  ZeroToClear,

  /// Write data bit of zero shall set (set to one) the corresponding bit in the field.
  ZeroToSet,

  /// Write data bit of zero shall toggle (invert) the corresponding bit in the field.
  ZeroToToggle,

  /// After a write operation, all the bits in the field are cleared (set to zero).
  Clear,

  /// After a write operation, all the bits in the field are set (set to one).
  Set,

  /// After a write operation, all the bits in the field may be modified (default).
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

/// Defines constraints for writing values to a field.
#[derive(Debug, Clone, PartialEq)]
pub enum WriteConstraintSpec {
  /// Only the values in the enumerated values list(s) of the field may be written.
  UseEnumeratedValues,

  /// Only integers within the bounds of the range (inclusive) may be written.
  Range(WriteConstraintRangeSpec),

  /// Only the last-read value can be written.
  WriteAsRead,

  /// There are no constraints on writing to the field. This variant is only constructed in cases
  /// where the SVD XML is illogical, for example like this:
  ///
  /// ```xml
  /// <writeConstraint>
  ///   <useEnumeratedValues>false</useEnumeratedValues>
  /// </writeConstraint>
  /// ```
  ///
  /// The XML is supposed to contain one of three mutually exclusive options, so it doesn't make
  /// sense if the option that it contains is set to `false`.
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

/// A range of values that can be written to a field. Writable values are integers that fall within
/// the `min` and `max` bounds (inclusive).
#[derive(Debug, Clone, PartialEq)]
pub struct WriteConstraintRangeSpec {
  /// Lowest value that can be written to a field.
  pub min: u32,

  /// Highest value that can be written to a field.
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

/// Defines whether an enumerated value may be read from a field, written to a field, or both.
#[derive(Debug, Clone, PartialEq)]
pub enum EnumeratedValueUsageSpec {
  /// The enumerated value may be read from the field, but not written to it.
  Read,

  /// The enumerated value may be written to the field, but not read from it.
  Write,

  /// The enumerated value may be both written to the field and read from it.
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

/// A set of values that can be written to and/or read from a field.
#[derive(Debug, Clone, PartialEq)]
pub struct EnumeratedValueSetSpec {
  preceding_path: String,
  register_path: String,
  derived_from: Option<String>,

  /// The name of the set of enumerated values.
  pub name: Option<String>,

  /// Whether the values in this set can be read from the field, written to it, or both.
  pub usage: Option<EnumeratedValueUsageSpec>,

  /// The list of values.
  pub values: Vec<EnumeratedValueSpec>,
}
impl EnumeratedValueSetSpec {
  pub(crate) fn new(
    ev: &EnumeratedValues,
    preceding_path: &str,
    register_path: &str,
  ) -> SvdExpanderResult<Self> {
    Ok(Self {
      preceding_path: preceding_path.to_owned(),
      register_path: register_path.to_owned(),
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

  /// The full path to the enumerated value set that this set inherits from (if any).
  pub(crate) fn derived_from_path(&self) -> SvdExpanderResult<Option<String>> {
    match self.derived_from {
      Some(ref df) => match df.contains(".") {
        true => {
          return Err(SvdExpanderError::new(
            "Qualified paths to enumerated value sets are not currently supported.",
          ))
        }
        false => Ok(Some(format!("{}.{}", self.register_path, df))),
      },
      None => Ok(None),
    }
  }

  /// The full path to this enumerated value set. Will be `None` if this set does not
  /// have a `name` (`name` is `None`).
  pub(crate) fn path(&self) -> Option<String> {
    match self.name {
      Some(ref n) => Some(format!("{}.{}", self.register_path, n)),
      None => None,
    }
  }

  pub(crate) fn clone_with_preceding_paths(
    &self,
    preceding_path: &str,
    register_path: &str,
  ) -> Self {
    Self {
      preceding_path: preceding_path.to_owned(),
      register_path: register_path.to_owned(),
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

/// A value that can be written to or read from a field (or both).
#[derive(Debug, Clone, PartialEq)]
pub struct EnumeratedValueSpec {
  /// The name of the value. Must be unique within the enumerated value set.
  pub name: String,

  /// A description of the value's meaning.
  pub description: Option<String>,

  /// The actual value to be written and/or read.
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

/// The actual content that can be written to or read from a field as part of
/// an enumerated value set.
#[derive(Debug, Clone, PartialEq)]
pub enum EnumeratedValueValueSpec {
  /// The bit value to be read or written.
  Value(u32),

  /// This value is a catch-all for any other values that are not explicitly listed.
  Default,
}
