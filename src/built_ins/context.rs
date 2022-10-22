/*!

Context Manipulation

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
use crate::built_ins::{collect_symbol_or_head_symbol, extract_condition, register_builtin};
#[allow(unused_imports)]#[allow(unused_imports)]
use crate::interner::resolve_str;
#[allow(unused_imports)]
use crate::logging::set_verbosity;


// We can use the same function for *Set and *SetDelayed, because the only difference is whether the arguments are
// evaluated, which is done before being passed to the built-in function. Convenient.

/// Implements calls matching the pattern
///     `UpSetDelayed[lhs_, rhs_]`
fn UpSetDelayed(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    "UpSetDelayed deferring to UpSet"
  );
  UpSet(arguments, original, context)
}

/// Implements calls matching the pattern
///     `SetDelayed[lhs_, rhs_]`
fn SetDelayed(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  Set(arguments, original, context)
}

/// Implements calls matching the pattern
///     `Set[lhs_, rhs_]`
fn Set(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  // Two arguments
  let pattern = &arguments[&SExpression::variable_static_str("lhs")];
  let rhs     = &arguments[&SExpression::variable_static_str("rhs")];

  let (rhs, condition): (Atom, Option<Atom>) = extract_condition(rhs.clone());

  let value = SymbolValue::Definitions {
    def: original,
    lhs: pattern.clone(),
    rhs: rhs.clone(),
    condition,
  };

  match context.set_down_value(pattern.name().unwrap(), value) {
    Ok(()) => {}
    Err(msg) => {
      // todo: Make a distinction between program and system errors.
      log(Channel::Error, 1, msg.as_str());
    }
  };

  hold(rhs)
}


/// Implements calls matching the pattern
///     `UpSet[lhs_, rhs_]`
fn UpSet(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  // Two arguments
  let pattern   = &arguments[&SExpression::variable_static_str("lhs")];
  let outer_rhs = &arguments[&SExpression::variable_static_str("rhs")];

  log(
    Channel::Debug,
    4,
    format!(
      "UpSet called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  let (rhs, condition): (Atom , Option<Atom>) = extract_condition(outer_rhs.clone());

  let value = SymbolValue::Definitions {
    def: original.clone(),
    lhs: pattern.clone(),
    rhs: rhs.clone(),
    condition,
  };

  for symbol in collect_symbol_or_head_symbol(pattern.clone()) {
    log(
      Channel::Debug,
      4,
      format!("Setting up-value {} for symbol {}", &original, resolve_str(symbol)).as_str(),
    );
    // Make an up-value for symbol
    match context.set_up_value(symbol, value.clone()) {
      Ok(()) => {}
      Err(msg) => {
        // todo: Make a distinction between program and system errors.
        log(
          Channel::Error,
          1,
          format!("Could not set up-value for {}: {}", resolve_str(symbol), msg).as_str()
        );
      }
    }
  };

  hold(outer_rhs.clone())
}

/// Returns a List of upvalues for the provided symbol
/// Implements calls matching the pattern
///     `UpValues[sym_]`
pub fn UpValues(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  // Two arguments
  let symbol = &arguments[&SExpression::variable_static_str("sym")];

  if let Atom::Symbol(name) = symbol {
    let record = context.get_symbol(*name);
    let children: Vec<Atom> = // the following match
        match record {
          Some(record) => record.up_values.iter().map(|sv| {
            match sv{
              SymbolValue::Definitions { def, .. } => hold(def.clone()),
              // todo: Handle case that built-in has a condition.
              SymbolValue::BuiltIn { pattern, .. } => {
                hold(
                  Atom::SExpression(Rc::new(
                    vec![
                      Symbol::from_static_str("RuleDelayed"),
                      pattern.clone(),
                      Symbol::from_static_str("BuiltIn")
                    ]
                  ))
                )
              }
            }
          }
          ).collect(),
          None => vec![]
        };
    SExpression::new(
      Symbol::from_static_str("List"),
      children
    )
  } else {
    log(
      Channel::Error,
      1,
      format!("Expected symbol, got {}", symbol).as_str()
    );
    original
  }
}

// todo: factor out code common to the `*Values` functions.
/// Returns a List of upvalues for the provided symbol
/// Implements calls matching the pattern
///     `DownValues[sym_]`
pub fn DownValues(arguments: SolutionSet, _original: Atom, context: &mut Context) -> Atom {
  // Two arguments
  let symbol = &arguments[&SExpression::variable_static_str("sym")];

  if let Atom::Symbol(name) = symbol {
    let record = context.get_symbol(*name);
    let children: Vec<Atom> = // the following match
        match record {
          Some(record) => {
            record.down_values.iter().map(|sv| {
              println!("{:?}", sv);
              match sv {
                SymbolValue::Definitions { def, .. } => def.clone(),
                // todo: Handle case that built-in has a condition.
                SymbolValue::BuiltIn { pattern, .. } => {
                  Atom::SExpression(Rc::new(
                    vec![
                      Symbol::from_static_str("RuleDelayed"),
                      pattern.clone(),
                      Symbol::from_static_str("BuiltIn"),
                    ]
                  ))
                }
              }
            }
            ).collect()
          },

          None => vec![]
        };

    hold(SExpression::new(
      Symbol::from_static_str("List"),
      children
    ))

  } else {
    log(
      Channel::Error,
      1,
      format!("Expected symbol, got {}", symbol).as_str()
    );
    Symbol::from_static_str("Null")
  }
}


pub(crate) fn register_builtins(context: &mut Context) {

  register_builtin!(Set, "Set[lhs_, rhs_]", Attribute::Protected.into(), context);
  register_builtin!(SetDelayed, "SetDelayed[lhs_, rhs_]", Attribute::Protected+Attribute::HoldRest, context);
  register_builtin!(UpSet, "UpSet[lhs_, rhs_]", Attribute::Protected.into(), context);
  register_builtin!(UpSetDelayed, "UpSetDelayed[lhs_, rhs_]", Attribute::Protected+Attribute::HoldRest, context);
  register_builtin!(UpValues, "UpValues[sym_]", Attribute::Protected.into(), context);
  register_builtin!(DownValues, "DownValues[sym_]", Attribute::Protected.into(), context);

}
