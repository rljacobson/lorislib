/*!

A string type.

Todo: Intern strings.

*/

use std::{
  cmp::Ordering,
  hash::Hasher,
  convert::From,
};
use fnv::FnvHasher;

use crate::{
  format::{
    Formattable,
    Formatter
  },
  normal_form::NormalFormOrder,
  expression::Expression
};

use super::Atom;


#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct StringLiteral(pub String);


impl Formattable for StringLiteral {
  fn format(&self, _formatter: &Formatter) -> String {
    format!("\"{}\"", self.0)
  }
}

impl NormalFormOrder for StringLiteral {
  fn cmp(&self, other: &Self) -> Ordering {
    self.0.cmp(&other.0)
  }
}

impl Atom for StringLiteral {
  fn hash(&self) -> u64 {
    // Strings don't cache their hash.
    // if self.cached_hash != 0 {
    //   return self.cached_hash;
    // }

    let mut hasher = FnvHasher::default();

    hasher.write(&[102, 206, 57 , 172, 207, 100, 198, 133]);
    hasher.write(self.0.as_bytes());

    let result       = hasher.finish();
    // self.cached_hash = result;

    result
  }

  fn to_expression(self) -> Expression {
    Expression::StringLiteral(self)
  }


}

impl From<&str> for StringLiteral {
  fn from(literal: &str) -> Self {
    StringLiteral(literal.to_string())
  }
}

impl From<String> for StringLiteral {
  fn from(string: String) -> Self {
    StringLiteral(string)
  }
}

impl From<StringLiteral> for Expression {
  fn from(literal: StringLiteral) -> Self {
    Expression::StringLiteral(literal)
  }
}


display_formattable_impl!(StringLiteral);
