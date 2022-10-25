/*!

The attributes of a function, e.g. `Flat`, `Listable`, ….

Attributes are implemented as a bitfield.

*/
#![allow(dead_code)]

use std::{
  ops::{Add, Index}
};
use std::iter::Sum;


use strum_macros::{Display, IntoStaticStr, EnumString, EnumIter};

#[derive(Copy, Clone, PartialEq, Eq, Display, IntoStaticStr, Debug, EnumString, EnumIter)]
#[repr(u32)]
pub enum Attribute {
  Commutative = 0,
  Associative,
  /// Can the function have a variable number of arguments
  Variadic,
  /// The identity function if given only one argument, `f(x)==f(f(x))==x`. `Plus`, for example.
  OneIdentity,
  /// The function should automatically be threaded over lists: `f[{a, b, c}] == {f[a], f[b], f[c]}`.
  Listable,
  ReadOnly,
  /// Attributes of the symbol cannot be changed.
  AttributesReadOnly,
  SequenceHold,

  /// This is an S-expression representing a variable.
  Variable,
  /// This is an S-expression representing a sequence variable.
  SequenceVariable,
  /// This is a real or an integer
  Numeric,

  //Orderless = 0, // Commutative
  //Flat, // Associative
  // OneIdentity,
  // Listable,
  Constant,
  NumericFunction,
  Protected,
  Locked,
  ReadProtected,
  HoldFirst,
  HoldRest,
  HoldAll,
  HoldAllComplete,
  NHoldFirst,
  NHoldRest,
  NHoldAll,
  // SequenceHold,
  Temporary,
  Stub,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct Attributes(pub u32);

// These exist solely to be static references, which the `Index` trait insists on requiring.
static ATTRIBUTE_SET: bool = true;
static ATTRIBUTE_UNSET: bool = false;

impl Index<u32> for Attributes {
  type Output = bool;

  fn index(&self, index: u32) -> &Self::Output {
    if (self.0 & (1 << (index as u32))) != 0 {
      &ATTRIBUTE_SET
    } else {
      &ATTRIBUTE_UNSET
    }
  }
}

impl Index<Attribute> for Attributes {
  type Output = bool;

  fn index(&self, index: Attribute) -> &Self::Output {
    if (self.0 & (1 << (index as u32))) != 0 {
      &ATTRIBUTE_SET
    } else {
      &ATTRIBUTE_UNSET
    }
  }
}

impl Default for Attributes {
  fn default() -> Self {
    Attributes(0)
  }
}

impl From<Attribute> for Attributes {
  fn from(attribute: Attribute) -> Self {
    Attributes(1u32 << attribute as u32)
  }
}

impl Attributes {
  pub fn new() -> Self {
    Attributes::default()
  }

  pub fn update(&mut self, attributes: Attributes) {
    self.0 |= attributes.0;
  }

  // region Convenience getters and setters

  pub fn get(&self, attribute: Attribute) -> bool {
    (self.0 & (1 << attribute as u32)) != 0
  }

  pub fn set(&mut self, attribute: Attribute) {
    self.0 = self.0 | (1 << attribute as u32)
  }

  pub fn reset(&mut self, attribute: Attribute) {
    self.0 = self.0 & !(1 << attribute as u32)
  }

  pub fn commutative(&self) -> bool {
    self.get(Attribute::Commutative)
  }

  pub fn associative(&self) -> bool {
    self.get(Attribute::Associative)
  }

  pub fn variadic(&self) -> bool {
    self.get(Attribute::Variadic)
  }

  pub fn variable(&self) -> bool {
    self.get(Attribute::Variable)
  }

  pub fn sequence_variable(&self) -> bool {
    self.get(Attribute::SequenceVariable)
  }

  pub fn one_identity(&self) -> bool {
    self.get(Attribute::OneIdentity)
  }

  pub fn listable(&self) -> bool {
    self.get(Attribute::Listable)
  }

  pub fn read_only(&self) -> bool {
    self.get(Attribute::ReadOnly)
  }

  pub fn attributes_read_only(&self) -> bool {
    self.get(Attribute::AttributesReadOnly)
  }

  pub fn sequence_hold(&self) -> bool {
    self.get(Attribute::SequenceHold)
  }

  pub fn numeric_function(&self) -> bool {
    self.get(Attribute::NumericFunction)
  }

  pub fn protected(&self) -> bool {
    self.get(Attribute::Protected)
  }


  // endregion

}

// region Attribute addition implementations.

impl Sum<Attributes> for Attributes {
  fn sum<I: Iterator<Item=Attributes>>(iter: I) -> Self {
    let mut attributes: Attributes = Attributes::default();
    for a in iter{
      attributes.update(a);
    }
    attributes
  }
}

impl Add<Attribute> for Attributes {
  type Output = Self;

  fn add(mut self, other: Attribute) -> Self {
    self.set(other);
    self
  }
}


impl Add<Attributes> for Attribute {
  type Output = Attributes;

  fn add(self, mut other: Attributes) -> Self::Output {
    other.set(self);
    other
  }
}


impl Add<Attribute> for Attribute {
  type Output = Attributes;

  fn add(self, other: Attribute) -> Self::Output {
    let mut out: Attributes = self.into();
    out.set(other);
    out
  }
}

impl Add for Attributes {
  type Output = Self;

  fn add(mut self, other: Self) -> Self {
    self.update(other);
    self
  }
}

// endregion

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn attribute_index() {
    let mut attributes = Attributes::new();

    attributes.set(Attribute::Commutative);
    attributes.set(Attribute::Variadic);
    attributes.set(Attribute::Listable);
    attributes.set(Attribute::Commutative);
    attributes.set(Attribute::AttributesReadOnly);

    assert!(attributes.commutative());
    assert!(!attributes.associative());
    assert!(attributes.variadic());
    assert!(!attributes.one_identity());
    assert!(attributes.listable());
    assert!(!attributes.read_only());
    assert!(attributes.attributes_read_only());
    assert!(!attributes.sequence_hold());
  }

  #[test]
  fn unset_attribute() {
    let mut attributes = Attributes(255);

    attributes.reset(Attribute::Commutative);
    attributes.reset(Attribute::Associative);
    attributes.reset(Attribute::Variadic);
    attributes.reset(Attribute::OneIdentity);
    attributes.reset(Attribute::Listable);
    attributes.reset(Attribute::ReadOnly);
    attributes.reset(Attribute::AttributesReadOnly);
    attributes.reset(Attribute::SequenceHold);

    assert!(!attributes.commutative());
    assert!(!attributes.associative());
    assert!(!attributes.variadic());
    assert!(!attributes.one_identity());
    assert!(!attributes.listable());
    assert!(!attributes.read_only());
    assert!(!attributes.attributes_read_only());
    assert!(!attributes.sequence_hold());
  }
}
