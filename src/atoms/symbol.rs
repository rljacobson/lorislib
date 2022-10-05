/*!

  A symbol is a ground term. Symbols can be constructed from strings.

*/

use std::{
  cmp::Ordering,
  fmt::Display,
  hash::Hasher,
};
use fnv::FnvHasher;

use crate::{
  expression::Expression,
  format::{Formattable, Formatter},
  normal_form::NormalFormOrder,
};

use super::Atom;

// Todo: Intern strings.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct Symbol(pub String);

impl Formattable for Symbol {
  fn format(&self, _formatter: &Formatter) -> String {
    self.0.clone()
  }
}

impl NormalFormOrder for Symbol {
  fn cmp(&self, other: &Self) -> Ordering {
    self.0.cmp(&other.0)
  }
}

impl Atom for Symbol {

  fn hash(&self) -> u64 {
    // Symbols do not cache their hash.
    // if self.cached_hash != 0 {
    //   return self.cached_hash;
    // }

    let mut hasher = FnvHasher::default();

    hasher.write(&[107, 10 , 247, 23 , 33 , 221, 163, 156]);
    hasher.write(self.0.as_bytes());

    let result       = hasher.finish();
    // self.cached_hash = result;

    result
  }

  fn to_expression(self) -> crate::expression::Expression {
    Expression::Symbol(self)
  }
}

impl From<&str> for Symbol {
  fn from(literal: &str) -> Self {
    Symbol(literal.to_string())
  }
}

impl From<String> for Symbol {
  fn from(string: String) -> Self {
    Symbol(string)
  }
}

impl From<Symbol> for Expression {
  fn from(symbol: Symbol) -> Self {
    Expression::Symbol(symbol)
  }
}

display_formattable_impl!(Symbol);
