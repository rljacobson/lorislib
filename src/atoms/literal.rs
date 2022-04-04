/*!

This is just a proof of concept, so literals are implemented as strings. That is, while
integers, floats, strings, and so forth are parsed distinctly, they are all just strings
internally, with no distinction between them.

*/

use std::{
  cmp::Ordering
};

use crate::{
  format::{
    Formatable,
    Formatter
  },
  normal_form::NormalFormOrder,
  expression::Expression
};

use super::Atom;


// Todo: Intern strings.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct Literal(pub String);


impl Formatable for Literal {
  fn format(&self, _formatter: &Formatter) -> String {
    self.0.clone()
  }
}

impl NormalFormOrder for Literal {
  fn cmp(&self, other: &Self) -> Ordering {
    self.0.cmp(&other.0)
  }
}

impl Atom for Literal {
  fn as_expression(self) -> crate::expression::Expression {
    Expression::Literal(self)
  }
}


impl From<&str> for Literal {
  fn from(literal: &str) -> Self {
    Literal(literal.to_string())
  }
}


impl From<String> for Literal {
  fn from(string: String) -> Self {
    Literal(string)
  }
}


impl From<Literal> for Expression {
  fn from(literal: Literal) -> Self {
    Expression::Literal(literal)
  }
}


display_formatable_impl!(Literal);
