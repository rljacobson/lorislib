#![allow(non_snake_case)]
/*!

Built-in constants and functions.

 */

use std::{
  rc::Rc
};
use std::collections::HashMap;
use std::ops::{AddAssign, Div, MulAssign, Neg};

use rug::{Integer as BigInteger, Float as BigFloat, Float, Assign, ops::AddFrom, Complete};
use rug::ops::CompleteRound;
use num_integer; // For num_integer::binomial

use crate::{
  matching::{
    display_solutions,
    SolutionSet
  },
  parse,
  atom::{
    Symbol,
    SExpression,
    SExpression::hold,
    Atom,
    AtomKind
  },
  attributes::{
    Attributes,
    Attribute
  },
  context::*,
  logging::{
    log,
    Channel
  },
  interner::{
    IString::from,
    IString
  },
  evaluate,
  matching::Matcher
};
#[allow(unused_imports)]
use crate::interner::resolve_str;
#[allow(unused_imports)]
use crate::logging::set_verbosity;

// todo: store this in the global context as an own-value.
pub const DEFAULT_REAL_PRECISION: u32 = 53;

pub static STANDARD_PREAMBLE: [&str; 14] = [
  // Definitions

  "NumberQ[n_]:=If[Head[n]==Real, True, If[Head[n]==Integer, True, False]]",
  "Subtract[x_, rest_]:=Plus[x, Minus[rest]]",
  "Sqrt[x_]:=Root[2, x]", // Poorly named, perhaps.
  "Ln[x_]:=Log[E, x]",
  "Exp[x_]:=Power[E, x]",

  // Simplifications
  "a_*x_ + b_*y_ ^:= (a + b)*x /; And[SameQ[x, y], NumberQ[a], NumberQ[b]]",
  "(a_*x_)/(b_*y_) ^:= a / b /; SameQ[x, y]",

  // Differentiation
  "D[x_, y_] := 0 /; NumberQ[x]",                                  // Constants. No matching on `Head`
  "D[x_, y_] := 1 /; SameQ[x, y]",                                // Identity
  "D[x_^n_, y_] ^:= n*x_^(n-1)*D[x, y] /; OccursQ[x, y]", // Power Rule,

  "D[Sin[x_], y_] ^:= Cos[x]*D[x, y] /; OccursQ[x, y]",
  "D[Cos[x_], y_] ^:= -Sin[x]*D[x, y] /; OccursQ[x, y]",
  "D[Tan[x_], y_] ^:= Sec[x]^2*D[x, y] /; OccursQ[x, y]",
  "D[Sec[x_], y_] ^:= Sec[x]*Tan[x]*D[x, y] /; OccursQ[x, y]",
];


//                        f(substitutions, original_expression, context) -> evaluated_expression
pub type BuiltinFn = fn(SolutionSet, Atom, &mut Context) -> Atom;

macro_rules! register_builtin {
  ($name:ident, $pattern:literal, $attributes:expr, $context:ident) => {
    {
      let value = SymbolValue::BuiltIn {
        pattern: parse($pattern).unwrap(),
        condition: None,
        built_in: $name,
      };
      $context.set_down_value_attribute(IString::from(stringify!($name)), value, $attributes);
    };
  }
}

pub(crate) fn register_builtins(context: &mut Context) {
  // todo: When is something read-only vs protected? What permissions should these symbols have?

  // region Attributes for functions without definition

  context.set_attribute(IString::from("RuleDelayed"), Attribute::Protected).ok();
  context.set_attribute(IString::from("RuleDelayed"), Attribute::HoldRest).ok();

  context.set_attribute(IString::from("List"), Attribute::Protected).ok();
  context.set_attribute(IString::from("Hold"), Attribute::Protected).ok();
  context.set_attribute(IString::from("Hold"), Attribute::HoldAll).ok();

  // endregion

  // region Constants
  // Todo: Implement NValues
/*
  // Numeric up_value for `Pi`
  { // Scope for pi_record
    let f = { // scope of children
      let children = [
        Symbol::from_static_str("UpSet"),
        Atom::SExpression(Rc::new(
          [
            Symbol::from_static_str("N"),
            Symbol::from_static_str("Pi")
          ].to_vec()
        )),
        Atom::Real(BigFloat::with_val(53, rug::float::Constant::Pi))
      ];
      Atom::SExpression(Rc::new(children.to_vec()))
    };

    evaluate(f, context);
    context.set_attribute(IString::from("Pi"), Attribute::Protected).unwrap();
  }
*/

  // endregion

  // region Preamble

  for n in 0..7  {
    let definition = parse(STANDARD_PREAMBLE[n]).unwrap();
    evaluate(definition, context);
  }


  // endregion

}

// region utilities

/// If `atom` has the form `Condition[exp1, exp2]`, gives `(exp1, Some(exp2))`. Otherwise, gives `(atom, None)`.
fn extract_condition(atom: Atom) -> (Atom, Option<Atom>) {
  match atom {

    Atom::SExpression(children)
      if children.len() == 3 && children[0] == Symbol::from_static_str("Condition")
      => {
      (children[1].clone(), Some(children[2].clone()))
    }

    _ => (atom, None)
  }
}

/// The `pattern_function` must be a function. Finds all symbols or symbols that are heads of functions that are
/// arguments to the given function.
fn collect_symbol_or_head_symbol(pattern_function: Atom) -> Vec<IString>{
  let f = SExpression::children(&pattern_function);
  let mut child_iter = f.iter();
  child_iter.next(); // skip head

  child_iter.filter_map(|c| {
    match c {
      Atom::Symbol(name) => Some(*name),
      Atom::SExpression(f)=> Some(f[0].name().unwrap()),
      _ => None
    }
  }).collect()
}

// endregion



#[cfg(test)]
mod tests {
  use crate::atom::{Atom, Symbol};
  use crate::attributes::{Attribute, Attributes};
  use crate::builtins::{extract_condition, occurs_check, Set};
  use crate::context::SymbolValue;
  use crate::interner::IString::from;
  use crate::{Context, parse};
  #[allow(unused_imports)]
  use crate::logging::set_verbosity;

  #[test]
  fn occurs_check_test() {
    let needle = Symbol::from_static_str("a");
    let haystack = parse("3.8*x^2 + 2*x^f[a+b, c*d, e]").unwrap();

    assert!(occurs_check(&needle, &haystack));

    let needle = Symbol::from_static_str("r");
    assert!(!occurs_check(&needle, &haystack));
  }

  #[test]
  fn register_builtins_test() {
    // This test succeeds if it doesn't panic.
    let _: Context = Context::new_global_context();
  }

  #[test]
  fn set_down_value_attribute_test(){
    // To avoid calling `register_builtins()`, which would make this test moot, we specially construct the context.
    let mut context             : Context    = Context::without_built_ins(IString::from("Global"));
    let mut read_only_attributes: Attributes = Attributes::default();
    // todo: when is something read-only vs protected?
    read_only_attributes.set(Attribute::ReadOnly);
    read_only_attributes.set(Attribute::AttributesReadOnly);

    // region Context Manipulation
    // Set[lhs_, rhs_]
    let value = SymbolValue::BuiltIn{
      pattern  : parse("Set[lhs_, rhs_]").unwrap(),
      condition: None,
      built_in : Set
    };
    context.set_down_value_attribute(IString::from("Set"), value.clone(), read_only_attributes);

    // Check.
    let record = context.get_symbol(IString::from("Set")).unwrap();
    assert_eq!(record.down_values[0], value);
  }

  #[test]
  fn extract_condition_test(){
    // Condition Present
    let atom    : Atom = parse("Condition[exp1, exp2]").unwrap();
    let expected: (Atom, Option<Atom>)
        = (Symbol::from_static_str("exp1"), Some(Symbol::from_static_str("exp2")));
    assert_eq!(extract_condition(atom), expected);

    // Condition Absent
    let atom = parse("3.8*f[1+x, y]").unwrap();
    assert_eq!(extract_condition(atom.clone()), (atom, None));
  }
}
