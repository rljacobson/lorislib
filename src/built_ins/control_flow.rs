/*!

Program Control Flow Built-ins

*/
#![allow(non_snake_case)]






 // For num_integer::binomial

use crate::{
  matching::{
    display_solutions,
    SolutionSet
  },
  parse,
  atom::{
    SExpression,
    Atom
  },
  attributes::{
    Attribute
  },
  context::*,
  logging::{
    log,
    Channel
  },
  interner::{
    interned_static
  },
  evaluate
};
use crate::atom::Symbol;
use super::register_builtin;
#[allow(unused_imports)]#[allow(unused_imports)]
use crate::interner::resolve_str;
#[allow(unused_imports)]
use crate::logging::set_verbosity;



/// Implements calls matching
///     `If[cond_, truepath_, falsepath_] := built-in[cond_, truepath_, falsepath_]`
pub(crate) fn If(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "If called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  // Three arguments
  let cond      = &arguments[&SExpression::variable_static_str("cond")];
  let truepath  = &arguments[&SExpression::variable_static_str("truepath")];
  let falsepath = &arguments[&SExpression::variable_static_str("falsepath")];

  // The condition has already been evalauted. We need only check its value.
  match cond {

    Atom::Symbol(name) if *name == interned_static("True") => {
      evaluate(truepath.clone(), context)
    }
    Atom::Symbol(name) if *name == interned_static("False") => {
      evaluate(falsepath.clone(), context)
    }

    _ => {
      // The condition is neither true nor false. Nothing to do.
      original
    }

  }
}


/// Implements calls matching
///     `CompoundExpression[exp___]`
pub(crate) fn CompoundExpression(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "CompoundExpression called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  // One argument
  let exp = &arguments[&SExpression::null_sequence_variable_static_str("exp")];

  if let Atom::SExpression(children) = exp {
    // Evaluate each non-head child, returning the result of the last one.
    let mut last_result = Symbol::from_static_str("Null");

    for child in children[1..].iter() {
      // todo: How do we stop on an error? We have no exception support yet.
      //       We keep evaluating unless the error is "critical".
      last_result = evaluate(child.clone(), context);
    }
    last_result
  } else {
    original
  }

}



pub(crate) fn register_builtins(context: &mut Context) {

  //If[cond_, truepath_, falsepath_] := BuiltIn
  register_builtin!(If, "If[cond_, truepath_, falsepath_]", Attribute::Protected+Attribute::HoldRest, context);
  register_builtin!(
    CompoundExpression, "CompoundExpression[exp___]", Attribute::Protected+Attribute::HoldAll, context
  );

}
