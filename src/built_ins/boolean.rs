/*!



 */
#![allow(non_snake_case)]
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
    interned_static,
    InternedString
  },
  evaluate,
  matching::Matcher
};
use crate::built_ins::register_builtin;
#[allow(unused_imports)]#[allow(unused_imports)]
use crate::interner::resolve_str;
#[allow(unused_imports)]
use crate::logging::set_verbosity;





/// Implements calls matching
///     `And[exp___] := built-in[exp]`
pub fn And(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "And called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  // Three cases:
  //   1. zero arguments -> True
  //   2. one argument -> identity
  //   3. A sequence of arguments -> computed.

  let  rhs = &arguments[&SExpression::null_sequence_variable_static_str("exp")];
  let mut new_children: Vec<Atom> = Vec::new();

  for child in SExpression::children(rhs)[1..].iter(){
    match child {

      Atom::Symbol(name) if *name == interned_static("True") => {
        // Don't add it to children.
        continue;
      }

      Atom::Symbol(name) if *name == interned_static("False")  => {
        // short circuiting
        return child.clone();
      }

      _ => {
        // Indeterminate
        new_children.push(child.clone())
      }

    }

  }

  match new_children.len() {

    // Equivalent to `And[]`
    0 => Symbol::from_static_str("True"),

    // Equivalent to `And[exp]`
    1 => new_children.pop().unwrap(),

    _ => {
      // Indeterminate
      SExpression::new(Symbol::from_static_str("And"), new_children)
    }
  }
}



/// Implements calls matching
///     `SameQ[exp___] := built-in[exp1, exp2]`
pub fn SameQ(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "SameQ called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  // Three cases:
  //   1. zero arguments -> True
  //   2. one argument -> True
  //   3. A sequence of arguments -> computed.

  let  rhs = &arguments[&SExpression::sequence_variable_static_str("exp")];

  // for child in SExpression::children(rhs)[1..].iter(){

  match rhs.len() {
    | 0
    | 1 => Symbol::from_static_str("True"),

    _many => {
      let children = SExpression::children(rhs);
      let mut arg_iter = children[1..].iter();
      let hash_value = arg_iter.next().unwrap().hashed();
      for child in arg_iter{
        if child.hashed() != hash_value {
          return Symbol::from_static_str("False");
        }
      }
      Symbol::from_static_str("True")
    }

  }
}


/// Implements calls matching
///     `Or[exp___] := built-in[exp]`
pub fn Or(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Or called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  // Three cases:
  //   1. zero arguments -> False
  //   2. one argument -> identity
  //   3. A sequence of arguments -> computed.

  let  rhs = &arguments[&SExpression::null_sequence_variable_static_str("exp")];
  let mut new_children: Vec<Atom> = Vec::new();

  for child in SExpression::children(rhs)[1..].iter(){
    match child {

      Atom::Symbol(name) if *name == interned_static("True") => {
        // short circuiting
        return child.clone();
      }

      Atom::Symbol(name) if *name == interned_static("False") => {
        // Don't add it to children.
        continue;
      }

      _ => {
        // Indeterminate
        new_children.push(child.clone())
      }

    }

  }

  match new_children.len() {

    // Equivalent to `Or[]`
    0 => Symbol::from_static_str("False"),

    // Equivalent to `Or[exp]`
    1 => new_children.pop().unwrap(),

    _ => {
      // Indeterminate
      SExpression::new(Symbol::from_static_str("Or"), new_children)
    }
  }
}

/// Implements calls matching
///     `Not[exp_] := built-in[exp]`
pub fn Not(arguments: SolutionSet, original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Not called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  // The argument is a single expression
  let rhs = &arguments[&SExpression::variable_static_str("exp")];
  match rhs {

    Atom::SExpression(children) if children[0]==Symbol::from_static_str("Not") =>{
      children[1].clone()
    }

    Atom::Symbol(name) if *name == interned_static("True") => {
      Symbol::from_static_str("False")
    }

    Atom::Symbol(name) if *name == interned_static("False") => {
      Symbol::from_static_str("True")
    }

    _ => original // Leave unevaluated
  }

}


pub(crate) fn register_builtins(context: &mut Context) {
  // A set of common attributes for convenience.
  let ac_function_attributes: Attributes
      = Attribute::Associative + Attribute::Commutative + Attribute::Protected + Attribute::Variadic;

  register_builtin!(And, "And[exp___]", ac_function_attributes, context);
  register_builtin!(Or, "Or[exp___]", ac_function_attributes, context);
  register_builtin!(SameQ, "SameQ[exp__]", Attribute::Protected+Attribute::Variadic+Attribute::Commutative, context);
  register_builtin!(Not, "Not[exp_]", Attribute::Protected.into(), context);

}
