/*!

  A symbol is a ground term. Symbols can be constructed from strings.

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


display_formatable_impl!(Symbol);
