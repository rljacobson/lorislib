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
  evaluate,
  abstractions::IString
};
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


// todo: store this in the global context as an own-value.
pub const DEFAULT_REAL_PRECISION: u32 = 53;

//                        f(substitutions, original_expression, context) -> evaluated_expression
pub type BuiltinFn = fn(SolutionSet, Atom, &mut Context) -> Atom;
/// The signature of the built-in functions that require mutable access to the context.
pub type BuiltinFnMut = fn(SolutionSet, Atom, &mut Context) -> Atom;

#[macro_export]
macro_rules! register_builtin {
  ($name:ident, $pattern:literal, $attributes:expr, $context:ident) => {
    {
      let value = SymbolValue::BuiltInMut {
        pattern: parse($pattern).unwrap(),
        condition: None,
        built_in: $name,
      };
      $context.set_down_value_attribute(IString::from(stringify!($name)), value, $attributes);
    };
  }
}
pub use register_builtin;

#[macro_export]
macro_rules! register_builtin_mut {
  ($name:ident, $pattern:literal, $attributes:expr, $context:ident) => {
    {
      let value = SymbolValue::BuiltInMut {
        pattern: parse($pattern).unwrap(),
        condition: None,
        built_in: $name,
      };
      $context.set_down_value_attribute(IString::from(stringify!($name)), value, $attributes);
    };
  }
}
pub use register_builtin_mut;


use crate::logging::{Channel, log};
use crate::matching::display_solutions;

// region Currently homeless built-ins

/// Sets the (global) verbosity level of the message logging system. Level 0 is off--not recommended. Level 1 is
/// "normal" enabled. Level 4 gives evaluation progress. Level 5 gives matching progress. Level n includes all
/// messages in levels m < n.
/// Implements calls matching
///     `SetVerbosity[exp_] := built-in[exp]`
pub(crate) fn SetVerbosity(arguments: SolutionSet, original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "SetVerbosity called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  // The argument is a single expression
  let  rhs = &arguments[&SExpression::variable_static_str("exp")];
  match rhs {

    Atom::Integer(n) => {
      set_verbosity(n.to_i32_wrapping());
      Symbol::from_static_str("Ok")
    }

    _ => {
      log(
        Channel::Error,
        1,
        "SetVerbosity must be called with an integer value."
      );
      original
    }
  }

}


// endregion

pub(crate) fn register_builtins(context: &mut Context) {
  // todo: When is something read-only vs protected? What permissions should these symbols have?

  register_control_flow(context);
  register_expressions(context);
  register_boolean(context);
  register_context(context);
  register_numeric(context);


  // region Attributes for functions without definition

  context.set_attribute(IString::from("List"), Attribute::Protected).ok();

  // endregion

  // region Preamble

  register_builtin!(SetVerbosity, "SetVerbosity[exp_]", Attribute::Protected.into(), context);

  let preamble_path = "./lorislib/lib/preamble.m";

  match std::fs::read_to_string(preamble_path){
    Ok(text) => {
      // set_verbosity(5);
      let expression = match parse(text.as_str()) {
        Ok(expression) => expression,
        Err(_) => {
          log(
            Channel::Error,
            1,
            format!("Failed to parse {}.", preamble_path).as_str()
          );
          return;
        }
      };
      // set_verbosity(4);
      evaluate(expression, context);
    }

    Err(e) => {
      log(
        Channel::Error,
        1,
        format!("Failed to read {}: {}", preamble_path, e).as_str()
      );
    }
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
pub fn collect_symbol_or_head_symbol(pattern_function: Atom) -> Vec<IString>{
  let f = SExpression::children(&pattern_function);
  let mut child_iter = f.iter();
  child_iter.next(); // skip head

  child_iter.filter_map(|c| {
    match c {
      Atom::Symbol(name) => Some(name.clone()),
      Atom::SExpression(f)=> {
        if c.is_any_variable_kind().is_some() {
          None
        } else {
          Some(f[0].name().unwrap())
        }
      },
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
    Context,
    parse
  };
  use crate::built_ins::context::Set;

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
    assert_eq!((&*record.down_values).borrow()[0], value);
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
