/*!

A sequence variable can be bound to a sequence of zero or more terms. Sequence variables
can be constructed from strings.

 */

use std::cmp::Ordering;
use std::hash::Hasher;
use fnv::FnvHasher;

use crate::{
  format::{
    Formattable,
    Formatter,
  },
  normal_form::NormalFormOrder,
  expression::Expression,
};

use super::Atom;


// Todo: Intern strings.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct SequenceVariable(pub String);


impl Formattable for SequenceVariable {
  fn format(&self, _formatter: &Formatter) -> String {
    format!("«{}»", self.0).to_string()
  }
}

impl NormalFormOrder for SequenceVariable {
  fn cmp(&self, other: &Self) -> Ordering {
    self.0.cmp(&other.0)
  }
}

impl Atom for SequenceVariable {
  fn hash(&self) -> u64 {
    // Symbols do not cache their hash.
    // if self.cached_hash != 0 {
    //   return self.cached_hash;
    // }

    let mut hasher = FnvHasher::default();

    hasher.write(&[57, 129, 46, 235, 112, 49, 134, 6]);
    hasher.write(self.0.as_bytes());

    let result = hasher.finish();
    // self.cached_hash = result;

    result
  }

  fn to_expression(self) -> Expression {
    Expression::SequenceVariable(self)
  }
}


impl From<&str> for SequenceVariable {
  fn from(literal: &str) -> Self {
    SequenceVariable(literal.to_string())
  }
}


impl From<String> for SequenceVariable {
  fn from(string: String) -> Self {
    SequenceVariable(string)
  }
}


impl From<SequenceVariable> for Expression {
  fn from(sequence_variable: SequenceVariable) -> Self {
    Expression::SequenceVariable(sequence_variable)
  }
}


display_formattable_impl!(SequenceVariable);



#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn formatted_variable() {
    let v = SequenceVariable("a".into());
    assert_eq!(v.format(&Formatter::default()), "«a»");
  }

  #[test]
  fn variable_from_things() {
    let v: SequenceVariable = "a".into();
    let u: SequenceVariable = String::from("a").into();
    assert_eq!(v, u);
  }

  #[test]
  fn expression_from_variable() {
    let v: SequenceVariable = SequenceVariable("a".into());
    let u: Expression = Expression::SequenceVariable(v.clone());
    let w: Expression = v.into();

    assert_eq!(u, w);
  }

  #[test]
  fn normal_form_ordering() {
    let v: SequenceVariable = SequenceVariable("albatross".into());
    let u: SequenceVariable = SequenceVariable("abacon".into());

    assert_eq!(NormalFormOrder::cmp(&v, &u), Ordering::Greater);
  }
}
