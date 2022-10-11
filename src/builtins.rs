#![allow(non_snake_case)]
/*!

Built-in constants and functions.

 */

use std::collections::HashMap;
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
use crate::{Expression, Parser, RcExpression};
use crate::attributes::{Attribute, Attributes};
use crate::context::*;
use crate::evaluate::evaluate;
use crate::logging::{Channel, log};
use crate::matching::SolutionSet;
// use std::f64::consts;


pub(crate) type BuiltinFn = fn(SolutionSet, &mut Context) -> RcExpression;

/*
pub static CONSTANTS: HashMap<&'static str, f64> = HashMap::from( [
  ( "Pi", std::f64::consts::PI ),
  ( "TAU", std::f64::consts::TAU ),
  ( "E", std::f64::consts::E ),

] );
*/

// N[exp_] := built-in[exp_]
// N[x] := built-in[{exp_->x}, context]
pub fn N(arguments: SolutionSet, ctx: &mut Context) -> RcExpression {
  // The substitutions represent the parameters to `N`. In the case of `N`, there is only on variable in the lhs
  // pattern, so we're applying `N` to  whatever the rhs expression is.
  // `N` has already been threaded over expressions, so we only need to act on our one argument.
  for (lhs, rhs) in arguments {
    log(
      Channel::Debug,
      5,
      format!("Built-in function N given argumetns: {:?}", (&lhs, &rhs)).as_str()
    );
    // There is guaranteed to be one and only one substitution.
    let expression = evaluate(rhs, ctx);
    match expression.as_ref() {

      Expression::Integer(Integer(n)) => {
        return Rc::new(Expression::Real(Real(*n as f64)));
      }

      _other => {
        return expression;
      }
    } // end match on evaluated rhs.
  }
  unreachable!("Built-in function `N` was called without arguments, which should be impossible. This is a bug.");
}

// UpSet[f_[___], rhs_]
fn up_set(arguments: SolutionSet, ctx: &mut Context) -> RcExpression {
  // Two arguments
  let arg_pairs: Vec<_> = arguments.into_iter().collect();
  let (_, pattern) = arg_pairs[0].clone();
  let (_, rhs) = arg_pairs[1].clone();

  let mut f = Function::with_symbolic_head("UpSet");
  f.children.push(pattern.clone());
  f.children.push(rhs.clone());
  let def: RcExpression = Rc::new(f.into());
  let value = SymbolValue::Definitions {
    def: def.clone(),
    lhs: pattern.clone(),
    rhs: rhs.clone()
  };

  for symbol in collect_symbol_or_head_symbol(pattern) {
    // Make an up-value for symbol
    ctx.set_up_value(symbol.name(), value.clone());
  };
  rhs
}



pub(crate) fn register_builtins(context: &mut Context) {
  let mut parser = Parser::new();

  // Numeric Floating Point Conversion
  // N[e_Integer]:=e_Real
  let value = SymbolValue::BuiltIn{
    pattern: parser.parse("N[e_]").unwrap(),
    built_in: N
  };
  let mut attributes = Attributes::default();
  attributes.set(Attribute::Listable);
  attributes.set(Attribute::ReadOnly);
  attributes.set(Attribute::AttributesReadOnly);
  context.set_down_value_attribute("N", value, attributes);

  // Numeric up_values for Pi`
  { // Scope for pi_record
    let mut pi_record = context.get_symbol("Pi");
    let f = Function::with_symbolic_head("UpSet");
    let value = SymbolValue::Definitions {
      def: Rc::new(f.into()),
      lhs: parser.parse("N[n_]").unwrap(),
      rhs: Rc::new(Real(std::f64::consts::PI).into()),
    };
    let mut attributes = Attributes::default();
    attributes.set(Attribute::ReadOnly);
    attributes.set(Attribute::AttributesReadOnly);
    pi_record.up_values.push(value);
    pi_record.attributes = attributes;
  }

}

// region utilities

/// The `pattern_function` must be a function`. Finds all symbols or symbols that are heads of functions that are
/// arguments to
/// the given function.
fn collect_symbol_or_head_symbol(pattern_function: RcExpression) -> Vec<RcExpression>{
  let f = Function::unwrap(pattern_function.as_ref());
  f.children.iter().filter_map(|c| {
    match c.as_ref() {
      Expression::Symbol(_) => Some(c.clone()),
      Expression::Function(f)=> Some(f.head.clone()),
      _ => None
    }
  }).collect()
}

// endregion

#[cfg(test)]
mod tests {
  #[test]
  fn it_works() {
    assert_eq!(2 + 2, 4);
  }
}
