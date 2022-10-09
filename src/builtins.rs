#![allow(non_snake_case)]
/*!

Built-in functions.

 */

use std::rc::Rc;
use crate::atoms::{
  Function,
  SequenceVariable,
  Sequence,
  Symbol,
  Variable,
  StringLiteral,
  Integer,
  Real,
};
use crate::{
  Expression,
  RcExpression
};
use crate::attributes::{Attribute, Attributes};
use crate::context::*;


pub(crate) type BuiltinFn = fn(this: RcExpression, _ctx: &mut Context) -> RcExpression;


pub fn N(this: RcExpression, _ctx: &mut Context) -> RcExpression {
  let function = Function::unwrap(this.as_ref());

  if function.children.len() == 1 {
    if let Expression::Integer(Integer(n)) = function.children.first().unwrap().as_ref() {
      return Rc::new(Expression::Real(Real(*n as f64)));
    }
  }

  this.clone()
}



pub(crate) fn register_builtins(context: &mut Context) {
  let value = SymbolValue::Builtin(N);
  let mut attributes = Attributes::default();
  attributes.set(Attribute::Listable);
  attributes.set(Attribute::ReadOnly);
  attributes.set(Attribute::AttributesReadOnly);
  context.set_down_value_attribute("N", value, attributes);
}

#[cfg(test)]
mod tests {
  #[test]
  fn it_works() {
    assert_eq!(2 + 2, 4);
  }
}
