/*!

  A symbol is a ground term. Symbols can be constructed from strings.

*/

use std::{
  fmt::Display,
  cmp::Ordering
};

use crate::{
  formatter::{
    Formatable,
    Formatter
  },
  normal_form::NormalFormOrder,
  expression::Expression
};

use super::Atom;


// Todo: Intern strings.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct Symbol(pub String);


impl Formatable for Symbol {
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
    fn as_expression(self) -> crate::expression::Expression {
        Expression::Symbol(self)
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format(&Formatter::default()))
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
