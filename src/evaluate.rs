/*!

Facilities for evaluating expressions within a context.

Evaluating an instance of `Replace` or `ReplaceAll` is equivalent to evaluating with a Context that is empty except
for the `OwnValues` the replacements represent.

`*Set` evaluates its RHS at definition time, while `*SetDelayed` evaluates its RHS at substitution time. All are
stored in the form `RuleDelayed[ HoldPattern[ lhs ], rhs ]`

Todo: implement scoping.

 */

use std::{
  rc::Rc
};
use crate::{
  context::SymbolValue,
  atom::Atom,
  matching::{Matcher, SolutionSet},
  logging::{log, Channel},
  context::Context
};
use crate::context::ContextValueStore;
use crate::interner::InternedString;

/// Evaluates `expression` in `context`.
pub fn evaluate(expression: Atom, context: &mut Context) -> Atom {
  // This function assumes the caller has already taken care of any `UpValues`.
  // Numbers and variables evaluate to themselves. It suffices to only take care
  // of the `Symbol` and `Function` cases.
  // let original_hash = expression.hash();

  match &expression {
    Atom::Symbol(symbol) => {
      // Look for OwnValues.

      if let Some(exp) = try_definitions(expression.clone(), *symbol, ContextValueStore::OwnValues, context) {
        return exp;
      }
      expression
    }

    Atom::SExpression(children) => {
      // Step 1: Look for `UpValues` for each child.
      // For UpValues, we match on the parent instead of the expression itself.
      log(Channel::Debug, 5, "Evaluating function. Checking for upvalues.");
      for child in children[1..].iter() {
        if let Some(name) = child.name() {
          if let Some(exp) = try_definitions(expression.clone(), name, ContextValueStore::UpValues, context) {
            // todo: Return here or..?
            return exp;
          }
        }
      }

      // Step 2: Evaluate all children.
      log(Channel::Debug, 5, "Evaluating children.");
      let mut new_children: Vec<Atom>
          = children.iter().map(|child| evaluate(child.clone(), context)).collect();
      // if original_hash != f.hash() {
      if new_children == *children.as_ref() {
        // We have changed the expression somehow, which might affect the application of UpValues. Abort this
        // evaluation in favor of evaluation of the new function.
        return evaluate(Atom::SExpression(Rc::new(new_children)), context);
      }

      // Step 3: Evaluate DownValues
      log(Channel::Debug, 5, "Looking for down values.");
      if let Some(name) = expression.name() {
        if let Some(exp) = try_definitions(expression.clone(), name, ContextValueStore::DownValues, context) {
          return exp;
        }
      }

      // Step 4: Done?
      expression
    } // end Atom::SExpression arm.

    any_other_expression => expression
  } // end match on Atom enum.

  // Ok(new_expression)
} // end evaluate.

/**
Evaluating rules with conditions is a bit meta, because evaluation is
defined in terms of evaluation. That is, to evaluate a rule, one must first
evaluate the condition. To break the infinite regress, most rules do not have
conditions, and most conditions are either simple or do not themselves have
conditions.
*/
fn check_condition(condition: Atom, substitutions: &SolutionSet, context: &mut Context)
    -> bool
{
  let condition_expression = replace_all(condition, substitutions);
  let condition_result = evaluate(condition_expression, context);
  condition_result.is_true()
}

fn try_definitions(expression: Atom, symbol: InternedString, value_store: ContextValueStore, context: &mut Context)
  -> Option<Atom>
{

  if let Some((symbol_value, substitutions))
    = find_matching_definition(expression.clone(), symbol, value_store, context){
    match symbol_value {
      SymbolValue::Definitions {rhs, condition,..} => {
        // Only try if the side condition is true
        if condition.is_none()
            || check_condition(condition.clone().unwrap(), &substitutions, context)
        {
          log(Channel::Debug, 5, format!("Doing substitutions for rhs = {}", rhs).as_str());
          Some(replace_all(rhs.clone(), &substitutions))
        } else {
          None
        }

      }
      SymbolValue::BuiltIn {built_in, condition,..} => {
        // Only try if the side condition is true
        if let Some(condition) = condition {
          if check_condition(condition.clone(), &substitutions, context) {
            log(Channel::Debug, 5, format!("Passing {:?} to built-in N", substitutions).as_str());
            Some(built_in(substitutions, expression, context))
          } else { None }
        } else {
          None
        }
      }
    }
  } else {
    None
  }

}

/// If any of the patterns in the vector of ``SymbolValue``'s match, return the RHS and the substitutions for the match.
fn find_matching_definition(ground: Atom, symbol: InternedString, value_store: ContextValueStore, context: &mut Context)
    -> Option<(SymbolValue, SolutionSet)>
{

  let definitions = {
    let record = context.get_symbol_mut(symbol);
    match value_store {
      ContextValueStore::OwnValues => &record.own_values,
      ContextValueStore::UpValues => &record.up_values,
      ContextValueStore::DownValues => &record.down_values,
      ContextValueStore::SubValues => &record.sub_values,
      _ => unimplemented!()
      // ContextValueStore::NValues => {}
      // ContextValueStore::DisplayFunction => {}
    }.clone() // todo: Get rid of this egregious clone.
  };

  if !definitions.is_empty() {
    log(Channel::Debug, 5, format!("Found {:?}.", value_store).as_str());
  }

  for symbol_value in definitions.iter() {
    log(Channel::Debug, 5, "Value found: ");
    let pattern =
      match symbol_value {

        SymbolValue::Definitions{lhs,..}=> {
          lhs
        }

        SymbolValue::BuiltIn {
          pattern,
          ..
        } => {
          pattern
        }

      };
    log(Channel::Debug, 5, format!("pattern = {}", (*pattern).to_string()).as_str());
    let mut matcher = Matcher::new(pattern.clone(), ground.clone(), context);
    if let Some(substitutions) = (&mut matcher).next() {
      log(Channel::Debug, 5, format!("Pattern matched!").as_str());
      return Some((symbol_value.clone(), substitutions));
    }
  } // end iterate over definitions
  None
}


/// Performs all substitutions in the given solution set on expression.
pub fn replace_all(expression: Atom, substitutions: &SolutionSet) -> Atom {
  match &expression {

    Atom::SExpression(children) => {
      // Do a `ReplaceAll` on the children
      let new_children =
          children.iter()
                  .map(|c| replace_all(c.clone(), substitutions))
                  .collect();

      Atom::SExpression(Rc::new(new_children))
    }


    expr if expr.is_any_variable_kind() => {
      match substitutions.get(&expression) {
        Some(e) => e.clone(),
        None    => expression
      }
    },

    _ => expression
  }
}


// pub fn apply(function: Atom, expression: Atom) -> Atom {
//   let mut f = Function::new(function);
//   f.children.push(expression);
//   Rc::new(f.into())
// }

/// Threads `Listable` functions, evaluates the `OneIdentity` property. Note that these two attributes are
/// mutually exclusive.
pub fn propogate_attributes(expression: Atom, context: &mut Context) -> Atom {
  match &expression {

    Atom::SExpression(children) => {
      let outer_head = children[0].clone();
      let record = context.get_symbol_mut(outer_head.name().unwrap());

      if record.attributes.listable() && children.len() == 2 {
        match &children[1] {
          Atom::SExpression(inner_children) => {
            let mut new_children = inner_children[0..1].to_vec();
            new_children.extend(
              inner_children[1..].iter()
                                 .map(|e| {
                                   // apply outer_head to e and recurse.
                                   propogate_attributes(
                                     Atom::SExpression(Rc::new(
                                       vec![outer_head.clone(), e.clone()]
                                     )),
                                     context
                                   )
                                 })
            );
            Atom::SExpression(Rc::new(new_children))
          } // end match to function

          _ => expression
        } // end match on only child.
      } // end if listable
      // OneIdentity
      else if record.attributes.one_identity() && children.len()==2 {
        propogate_attributes(children[0].clone(), context)
      } else {
        expression
      }

    }

    _ => expression
  }
}



#[cfg(test)]
mod tests {
  #![allow(non_snake_case)]
  use crate::context::Context;
  use crate::parsing::Parser;
  use super::*;

  #[test]
  fn eval_built_in_N() {
    let mut parser = Parser::default();
    let unevaluated = parser.parse("N[2]").unwrap();
    let expected = parser.parse("2.0").unwrap();
    let mut root_context = Context::new_global_context();

    let evaluated = evaluate(unevaluated, &mut root_context);

    assert_eq!(evaluated, expected);
  }
}

