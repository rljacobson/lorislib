/*!

A variable can be bound to a term, but not to a sequence of terms. Variables
can be constructed from strings.

Mote: A variable is a pattern, not what is normally called a variable in mathematics. Words and letters representing
unspecified numbers (or expressions generally) are called Symbols. Symbols correspond to mathematical variables.

 */

use std::{
  cmp::Ordering
};
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
pub struct Variable(pub String);


impl Variable {
  pub fn new(name: &str) -> Variable {
    Variable(name.to_string())
  }
}


impl Formattable for Variable {
  fn format(&self, _formatter: &Formatter) -> String {
    format!("‹{}›", self.0).to_string()
  }
}

impl NormalFormOrder for Variable {
  fn cmp(&self, other: &Self) -> Ordering {
    self.0.cmp(&other.0)
  }
}

impl Atom for Variable {
  fn hash(&self) -> u64 {
    // Variables do not cache their hash.
    // if self.cached_hash != 0 {
    //   return self.cached_hash;
    // }

    let mut hasher = FnvHasher::default();

    hasher.write(&[5, 15, 105, 181, 241, 116, 76, 166]);
    hasher.write(self.0.as_bytes());

    let result = hasher.finish();
    // self.cached_hash = result;

    result
  }

  fn to_expression(self) -> crate::expression::Expression {
    Expression::Variable(self)
  }
}


impl From<&str> for Variable {
  fn from(literal: &str) -> Self {
    Variable(literal.to_string())
  }
}


impl From<String> for Variable {
  fn from(string: String) -> Self {
    Variable(string)
  }
}


impl From<Variable> for Expression {
  fn from(variable: Variable) -> Self {
    Expression::Variable(variable)
  }
}


display_formattable_impl!(Variable);



#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn formatted_variable() {
    let v = Variable("a".into());
    assert_eq!(v.format(&Formatter::default()), "‹a›");
  }

  #[test]
  fn variable_from_things() {
    let v: Variable = "a".into();
    let u: Variable = String::from("a").into();
    assert_eq!(v, u);
  }

  #[test]
  fn expression_from_variable() {
    let v: Variable = Variable("a".into());
    let u: Expression = Expression::Variable(v.clone());
    let w: Expression = v.into();

    assert_eq!(u, w);
  }

  #[test]
  fn normal_form_ordering() {
    let v: Variable = Variable("albatross".into());
    let u: Variable = Variable("bacon".into());

    assert_eq!(NormalFormOrder::cmp(&v, &u), Ordering::Less);
  }
}
