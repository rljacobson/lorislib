/*!


Built-in constants and functions.

Todo: Implement NValues
Todo: Implement Constants

 */
#![allow(non_snake_case)]

use crate::{
  matching::{
    SolutionSet
  },
  parse,
  atom::{
    Symbol,
    SExpression,
    Atom
  },
  attributes::{
    Attribute
  },
  context::*,
  interner::{
    interned_static,
    InternedString
  },
  evaluate
};
#[allow(unused_imports)]#[allow(unused_imports)]
use crate::interner::resolve_str;
#[allow(unused_imports)]
use crate::logging::set_verbosity;


mod control_flow;
mod expressions;
mod boolean;
mod context;
mod numeric;



use control_flow::register_builtins as register_control_flow;
use expressions::register_builtins as register_expressions;
use boolean::register_builtins as register_boolean;
use context::register_builtins as register_context;
use numeric::register_builtins as register_numeric;

pub(crate) use context::Set;


// todo: store this in the global context as an own-value.
pub const DEFAULT_REAL_PRECISION: u32 = 53;

// region Preamble
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
  "D[x_^n_, y_] ^:= n*x_^(n-1)*D[x, y] /; Occurs[y, x]", // Power Rule,

  "D[Sin[x_], y_] ^:= Cos[x]*D[x, y] /; Occurs[y, x]",
  "D[Cos[x_], y_] ^:= -Sin[x]*D[x, y] /; Occurs[y, x]",
  "D[Tan[x_], y_] ^:= Sec[x]^2*D[x, y] /; Occurs[y, x]",
  "D[Sec[x_], y_] ^:= Sec[x]*Tan[x]*D[x, y] /; Occurs[y, x]",
];
// endregion

//                        f(substitutions, original_expression, context) -> evaluated_expression
pub type BuiltinFn = fn(SolutionSet, Atom, &mut Context) -> Atom;

#[macro_export]
macro_rules! register_builtin {
  ($name:ident, $pattern:literal, $attributes:expr, $context:ident) => {
    {
      let value = SymbolValue::BuiltIn {
        pattern: parse($pattern).unwrap(),
        condition: None,
        built_in: $name,
      };
      $context.set_down_value_attribute(interned_static(stringify!($name)), value, $attributes);
    };
  }
}
pub use register_builtin;

pub(crate) fn register_builtins(context: &mut Context) {
  // todo: When is something read-only vs protected? What permissions should these symbols have?

  register_control_flow(context);
  register_expressions(context);
  register_boolean(context);
  register_context(context);
  register_numeric(context);


  // region Attributes for functions without definition

  context.set_attribute(interned_static("RuleDelayed"), Attribute::Protected).ok();
  context.set_attribute(interned_static("RuleDelayed"), Attribute::HoldRest).ok();

  context.set_attribute(interned_static("List"), Attribute::Protected).ok();
  context.set_attribute(interned_static("Hold"), Attribute::Protected).ok();
  context.set_attribute(interned_static("Hold"), Attribute::HoldAll).ok();

  context.set_attribute(interned_static("UpValues"), Attribute::HoldAll).ok();
  context.set_attribute(interned_static("DownValues"), Attribute::HoldAll).ok();
  context.set_attribute(interned_static("OwnValues"), Attribute::HoldAll).ok();

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
pub fn extract_condition(atom: Atom) -> (Atom, Option<Atom>) {
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
pub fn collect_symbol_or_head_symbol(pattern_function: Atom) -> Vec<InternedString>{
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


/// This version of occurs check is called directly with two atoms. If the expression `needle` occurs anywhere in the
/// expression `haystack`, returns true. Otherwise, returns false.
pub fn occurs_check(needle: &Atom, haystack: &Atom) -> bool {
  let needle_hash = needle.hashed();
  if needle_hash == haystack.hashed() {
    return true;
  }

  if let Atom::SExpression(children) = haystack {
    for child in (*children).iter() {
      if occurs_check(&needle, child) {
        return true;
      }
    }
  };

  false
}


// endregion



#[cfg(test)]
mod tests {
  use crate::{
    context::SymbolValue,
    attributes::{Attribute, Attributes},
    atom::{Atom, Symbol},
    interner::interned_static,
    Context,
    parse
  };

  use super::*;

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
    let mut context             : Context    = Context::without_built_ins(interned_static("Global"));
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
    context.set_down_value_attribute(interned_static("Set"), value.clone(), read_only_attributes);

    // Check.
    let record = context.get_symbol(interned_static("Set")).unwrap();
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