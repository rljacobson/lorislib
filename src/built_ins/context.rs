/*!

Context Manipulation

Todo: Should a lot of these functions be factored out into methods on `Context`?

*/
#![allow(non_snake_case)]

use std::{
  cmp::max,
  rc::Rc,
  str::FromStr
};

use strum::{IntoEnumIterator};


// For num_integer::binomial

use crate::{atom::SExpression::extract_thing_or_list_of_things, matching::{
  display_solutions,
  SolutionSet
}, parse, atom::{
  Symbol,
  SExpression,
  SExpression::hold,
  Atom
}, attributes::{
  Attribute,
  Attributes as SymbolAttributes, // Name collision with the built-in "Attributes"
}, context::*, logging::{
  log,
  Channel
}, interner::{
  interned_static
}, interner::InternedString, interner::resolve_str, register_builtin_mut};
#[allow(unused_imports)]
use crate::logging::set_verbosity;

use super::{
  collect_symbol_or_head_symbol,
  extract_condition,
  register_builtin
};


// We can use the same function for *Set and *SetDelayed, because the only difference is whether the arguments are
// evaluated, which is done before being passed to the built-in function. Convenient.

/// Implements calls matching the pattern
///     `UpSetDelayed[lhs_, rhs_]`
pub(crate) fn UpSetDelayed(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    "UpSetDelayed deferring to UpSet"
  );
  UpSet(arguments, original, context)
}

/// Implements calls matching the pattern
///     `SetDelayed[lhs_, rhs_]`
pub(crate) fn SetDelayed(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  Set(arguments, original, context)
}

/// Implements calls matching the pattern
///     `Set[lhs_, rhs_]`
pub(crate) fn Set(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
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

  // If pattern is a symbol, not a function, then this is an OwnValue we are setting.
  if let Atom::Symbol(_name) = pattern {

    match context.set_own_value(pattern.name().unwrap(), value) {
      Ok(()) => {}
      Err(msg) => {
        // todo: Make a distinction between program and system errors.
        log(Channel::Error, 1, msg.as_str());
      }
    };

  } else {

    match context.set_down_value(pattern.name().unwrap(), value) {
      Ok(()) => {}
      Err(msg) => {
        // todo: Make a distinction between program and system errors.
        log(Channel::Error, 1, msg.as_str());
      }
    };

  }

  hold(rhs)
}


/// Implements calls matching the pattern
///     `UpSet[lhs_, rhs_]`
pub(crate) fn UpSet(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
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
pub(crate) fn UpValues(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
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
              | SymbolValue::BuiltIn { pattern, .. }
              | SymbolValue::BuiltInMut { pattern, .. } => {
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
pub(crate) fn DownValues(arguments: SolutionSet, _original: Atom, context: &mut Context) -> Atom {
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
                | SymbolValue::BuiltIn { pattern, .. }
                | SymbolValue::BuiltInMut { pattern, .. } => {
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


/// Implements calls matching the pattern
///     `SetAttributes[sym_, attr_]`
pub(crate) fn SetAttributes(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  // Two arguments
  let symb: &Atom = &arguments[&SExpression::variable_static_str("sym")];
  let attr = &arguments[&SExpression::variable_static_str("attr")];

  // symb is either a symbol or a list of symbols. Normalize to a `Vec<InternedString>`
  let symbols: Vec<InternedString> =
      extract_thing_or_list_of_things(symb, |e| e.name());
  // Error check: Was every child a thing that has a name?
  if symbols.len() != max(symb.len(), 1) {
    // If symb is a single thing, max(…) == 1, and if symb is a NONEMPTY list of things, `max(…)` needs to be the
    // length of that list. If the if-condition is violated, then either we were given an empty list or we were given
    // things without names.
    log(
      Channel::Error,
      1,
      format!("Expected a list of symbols, got {}", symb).as_str()
    );
    return original;
  }

  // attr is either an `Attribute` or a list of attributes.
  let attributes_list: Vec<SymbolAttributes> = {
    // Good grief.
    let a_strs: Vec<InternedString> = extract_thing_or_list_of_things(attr, |e| e.name());
    a_strs.iter()
        .filter_map(|s| Attribute::from_str(resolve_str(*s)).ok())
        .map(|a| a.into()).collect()
  };

  // Error check - see previous for explanation.
  if attributes_list.len() != max(attr.len(), 1) {
    log(
      Channel::Error,
      1,
      format!("Expected a list of attributes, got {}", attr).as_str()
    );
    return original;
  }

  let attributes: SymbolAttributes = attributes_list.into_iter().map(|a| a.into()).sum();

  // For each symbol, set all attributes.
  for name in symbols {
    if let Err(reason) = context.set_attributes(name, attributes){
      log(
        Channel::Error,
        1,
        format!("Failed to set attributes for symbol {}: {}", resolve_str(name), reason).as_str()
      );
    };
  }

  Symbol::from_static_str("Ok")
}


/// Returns a List of upvalues for the provided symbol
/// Implements calls matching the pattern
///     `Attributes[sym_]`
pub(crate) fn Attributes(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  // Two arguments
  let symbol = &arguments[&SExpression::variable_static_str("sym")];

  if let Atom::Symbol(name) = symbol {
    let found_attributes = context.get_attributes(*name);
    let mut children = vec![Symbol::from_static_str("List")];
    children.extend(
      Attribute::iter()
          .filter_map(|attr| {
            if found_attributes.get(attr){
              Some(attr)
            } else {
              None
            }
          })
          .map(|a|{
            Symbol::from_static_str(a.into())
          })
    );
    Atom::SExpression(Rc::new(children))
  } else {
    log(
      Channel::Error,
      1,
      format!("Expected symbol, got {}", symbol).as_str()
    );
    original
  }
}





pub(crate) fn register_builtins(context: &mut Context) {
  let delayed_functions: SymbolAttributes = Attribute::Protected + Attribute::HoldAll + Attribute::SequenceHold;
  let set_functions: SymbolAttributes = Attribute::Protected + Attribute::HoldFirst;
  let holdall_protected: SymbolAttributes = Attribute::Protected + Attribute::HoldAll;


  context.set_attributes(
    interned_static("RuleDelayed"),
    Attribute::HoldRest  // Why not HoldAll?
        + Attribute::SequenceHold
        + Attribute::Protected
  ).ok();
  context.set_attributes(
    interned_static("Rule"),
        Attribute::SequenceHold
        + Attribute::Protected
  ).ok();
  context.set_attributes(interned_static("Hold"), holdall_protected).ok();
  context.set_attributes(interned_static("OwnValues"), holdall_protected).ok();

  register_builtin!(Set, "Set[lhs_, rhs_]", set_functions, context);
  register_builtin!(SetDelayed, "SetDelayed[lhs_, rhs_]", delayed_functions, context);
  register_builtin!(UpSet, "UpSet[lhs_, rhs_]", set_functions, context);
  register_builtin!(UpSetDelayed, "UpSetDelayed[lhs_, rhs_]", delayed_functions, context);
  register_builtin!(UpValues, "UpValues[sym_]", holdall_protected, context);
  register_builtin!(DownValues, "DownValues[sym_]", holdall_protected, context);
  register_builtin!(SetAttributes, "SetAttributes[sym_, attr_]", holdall_protected, context);
  register_builtin!(Attributes, "Attributes[sym_]", holdall_protected, context);

}
