/*!

  A variable can be bound to a term, but not to a sequence of terms. Variables
  can be constructed from strings.

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
pub struct Variable(pub String);


impl Variable {
  pub fn new(name: &str) -> Variable {
    Variable(name.to_string())
  }
}


impl Formatable for Variable {
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
    fn as_expression(self) -> crate::expression::Expression {
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


display_formatable_impl!(Variable);



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
