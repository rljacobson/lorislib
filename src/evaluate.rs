/*!

Facilities for evaluating expressions within a context.

Evaluating an instance of `Replace` or `ReplaceAll` is equivalent to evaluating with a Context that is empty except
for the `OwnValues` the replacements represent.

`*Set` evaluates its RHS at definition time, while `*SetDelayed` evaluates its RHS at substitution time. All are
stored in the form `RuleDelayed[ HoldPattern[ lhs ], rhs ]`

Todo: implement scoping.

ToDo: Evaluate needs to know when it is finished. See notes below. If we can keep an expressions `evaluated_version`
      on the stack during recursion, we won't need to store it as a property of the expression, which means only simple
      code changes.

Evaluation continues until it reaches a fixed point. But it is inefficient to re-evaluate everything a second time
if it doesn't need it. An expression needs to know when it is completely evaluated. If it has already searched
through the `Context` and found no applicable rules, it can set a flag on itself indicating it is completely
evaluated. The problem is, if `context` has been modified during evaluation, it could make the expression no
longer be in the "fully evaluated" state. One reasonable solution is to keep a "version" property in `Context`
that is incremented every time `context` is modified. (Finer-grained versioning might also be possible but seems
unlikely to be of benefit given modification of `context` is likely to be rare.) That version is then used as
the "fully modified state" indicator. If `expr.evaluated_version < context.version`, it is evaluated again.

*/

use std::{
  rc::Rc
};

use crate::{context::SymbolValue, atom::{
  Atom,
  SExpression,
  Symbol
}, matching::{
  Matcher,
  SolutionSet,
  display_solutions
}, logging::{log, Channel}, context::Context, attributes::{Attribute, Attributes}, context::ContextValueStore, interner::{InternedString, resolve_str}, context};


pub fn evaluate(expression: Atom, context: &mut Context) -> Atom {
  /*
  The general strategy is to apply an operation to an expression, see if it has changed, and if it has, to evaluate
  again, until the expression reaches a fixed-point.

  Todo: Add recursion-limit
  Todo: Add cycle detection

  */

  // This function assumes the caller has already taken care of any `UpValues`.
  // Numbers and variables evaluate to themselves. It suffices to only take care
  // of the `Symbol` and `Function` cases.
  match &expression {

    Atom::Symbol(symbol) => {
      // Look for OwnValues.
      // log(Channel::Debug, 4, "Evaluating symbol. Checking for own-values.");

      let original_hash = expression.hashed();
      // The "state version" of `context` that this expression was last evaluated at.
      let evaluated_version = context.state_version();

      if let Some(exp) = try_definitions(
        expression.clone(),
        *symbol,
        ContextValueStore::OwnValues,
        context
      ) {
        if exp.hashed() != original_hash || evaluated_version != context.state_version() {
          // Something has changed, so continue evaluating.
          evaluate(exp, context)
        } else {
          exp
        }
      } else {
        // No own-values. Return original expression.
        expression
      }
    } // end Atom::Symbol branch

    Atom::SExpression(children) => {
      let original_hash = expression.hashed();
      // The "state version" of `context` that this expression was last evaluated at.
      let evaluated_version = context.state_version();

      // If the head is a name with `Hold*` attributes, we are not allowed to evaluate some or all of the children.
      // In order to have attributes, the head needs to have a name in the first place. We do this in a single step.
      let name_and_hold_attribute: Option<(InternedString, Attribute)> =
          match &expression.name() {
            Some(name) => {
              let attributes = context.get_attributes(*name);
              // It is convenient to have attributes be a statically matchable value.
              // The following are precisely the conditions needed in the match arms below.
              let attribute =
                  if attributes[Attribute::HoldFirst]
                      && children.len() > 1 // There needs to be a "first" to hold.
                  {
                    Attribute::HoldRest
                  } else if attributes[Attribute::HoldRest]
                      && children.len() > 2 // There needs to be a "rest" to hold.
                  {
                    Attribute::HoldFirst
                  } else if attributes[Attribute::HoldAll]
                      || attributes[Attribute::HoldAllComplete]
                  {
                    Attribute::HoldAll
                  } else{
                    // Some arbitrary value
                    Attribute::Stub
                  };

              Some((*name, attribute))
            } // end if name branch

            _ => {
              None
            }
          }; // end match on expression.name()

      // In each match branch for `name_and_hold_attribute`, we do two this:
      //    1. Look for `UpValues` for each unheld child.
      //    2. Evaluate each unheld child.
      let new_expression =
        match name_and_hold_attribute {

          Some((_name, Attribute::HoldFirst)) => {
            // Step 1: Look for `UpValues` for each unheld child.
            // For UpValues, we match on the parent instead of the child expression that is associated with the up-value.
            // log(Channel::Debug, 4, "Evaluating function. Checking for upvalues.");
            if let Some(new_expression) = evaluate_up_values(&expression, &children[2..], context){
              new_expression
            }
            // No applicable up-values.
            // Step 2: Evaluate children.
            else {
              let mut evaluated_children = Vec::with_capacity(children.len());
              evaluated_children.push(children[0].clone()); // This is expression.head()
              evaluated_children.push(children[1].clone()); // ...and the first child
              evaluated_children.extend(
                children[2..].iter().cloned().map(|exp| evaluate(exp, context))
              );
              Atom::SExpression(Rc::new(evaluated_children))
            }
          } // end HoldFirst branch

          Some((_name, Attribute::HoldRest)) => {
            // Step 1: Look for `UpValues` for each unheld child.
            // For UpValues, we match on the parent instead of the child expression that is associated with the up-value.
            // log(Channel::Debug, 4, "Evaluating function. Checking for up-values.");
            if let Some(new_expression) = evaluate_up_values(&expression, &children[1..2], context){
              new_expression
            }
            // No applicable up-values.
            // Step 2: Evaluate children.
            else {
              let mut evaluated_children = Vec::with_capacity(children.len());
              evaluated_children.push(evaluate(children[0].clone(), context)); // This is expression.head()
              evaluated_children.push(evaluate(children[1].clone(), context)); // ...and the first child
              evaluated_children.extend(children[2..].iter().cloned());
              Atom::SExpression(Rc::new(evaluated_children))
            }
          }

          Some((_name, Attribute::HoldAll)) => {
            // The silliest case: We cannot evaluate anything–a no-op!
            expression
          }

          _ => {
            // No restrictions – evaluate everything
            // Step 1: Look for `UpValues` for each unheld child.
            // For UpValues, we match on the parent instead of the child expression that is associated with the up-value.
            // log(Channel::Debug, 4, "Evaluating function. Checking for up-values.");
            if let Some(new_expression) = evaluate_up_values(&expression, &children[1..], context){
              new_expression
            }
            // No applicable up-values.
            // Step 2: Evaluate children.
            else {
              let mut evaluated_children
                  = children.iter()
                            .map(|child| evaluate(child.clone(), context))
                            .collect::<Vec<_>>();
              Atom::SExpression(Rc::new(evaluated_children))
            }
          } // end None branch

        }; // end match on name_and_hold_attribute

      // If steps 1 or 2 were successful, then we changed the expression somehow.
      if new_expression.hashed() != original_hash || evaluated_version != context.state_version() {
        log(
          Channel::Debug,
          4,
          "Evaluating up-values and children changed the expression. Evaluating again."
        );
        // We have changed the expression or the context somehow, which
        // might affect the application of UpValues. Abort this evaluation in favor of evaluation of the new function.
        return evaluate(new_expression, context);
      }

      // Step 3: Evaluate DownValues.
      // We can only have down-values if the head has a name.
      if let Some((name, _)) = name_and_hold_attribute {
        log(Channel::Debug, 4, "Looking for down values.");
        if let Some(new_expression) = try_definitions(
          new_expression.clone(),
          name,
          ContextValueStore::DownValues,
          context
        ) {
          if original_hash != new_expression.hashed()
              || evaluated_version != context.state_version()
          {
            log(
              Channel::Debug,
              4,
              "Evaluating DownValue changed the expression. Evaluating again."
            );
            evaluate(new_expression, context)
          } else {
            log(
              Channel::Debug,
              4,
              "Evaluating DownValue left expression unchanged. Returning."
            );
            new_expression
          }
        } else {
          new_expression
        }
      } else {
        // No name, no DownValues.
        new_expression
      }
    } // end if expression is an s-expression

    _ => expression
  }
}

/// Given an `expression` and a list of only its unheld `children`, returns the result of the first matching
/// up-value, or None if there are no matching up-values.
fn evaluate_up_values(expression: &Atom, children: &[Atom], context: &mut Context) -> Option<Atom> {
  for child in children.iter() {
    if let Some(name) = child.name() {
      if let Some(exp) = try_definitions(expression.clone(), name, ContextValueStore::UpValues, context) {
        // An up-value modifies this parent expression, so if a single up-value applies, return the new modified
        // expression.
        return Some(exp);
      }
    }
  }
  None
}

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
  let condition_expression = replace_all_bound_variables(condition, substitutions, context);
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
          log(Channel::Debug, 4, format!("Doing substitutions for rhs = {}", &rhs).as_str());
          let replaced  = replace_all_bound_variables(rhs, &substitutions, context);
          log(Channel::Debug, 4, format!("After replacement: {}", &replaced).as_str());
          Some(replaced)
        } else {
          log(
            Channel::Debug,
            4,
            "Failed condition branch for SymbolValue::Definitions",
          );
          None
        }

      }
      SymbolValue::BuiltIn {built_in, condition,..} => {
        log(
          Channel::Debug,
          4,
          "Found BuiltIn",
        );
        // Only try if the side condition is true
        if let Some(condition) = condition {
          log(
            Channel::Debug,
            4,
            "Some(condition) branch for SymbolValue::BuiltIn",
          );
          if check_condition(condition.clone(), &substitutions, context) {
            log(
              Channel::Debug,
              4,
              format!("Passing {} to built-in function", display_solutions(&substitutions)).as_str()
            );
            Some(built_in(substitutions, expression, context))
          } else {
            log(
              Channel::Debug,
              4,
              "Failed to pass condition branch for SymbolValue::BuiltIn",
            );
            None
          }
        } else {
          // No condition. Just execute.
          log(
            Channel::Debug,
            4,
            format!("Passing {} to built-in function", display_solutions(&substitutions)).as_str()
          );
          Some(built_in(substitutions, expression, context))
        }
      }
    }
  } else {
    // log(
    //   Channel::Debug,
    //   4,
    //     "No definitions found by find_matching_definition()",
    // );
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
    log(Channel::Debug, 4, format!("Found {:?}.", value_store).as_str());
  } else {
    log(
      Channel::Debug,
      4,
      format!("No {:?} for symbol {}.", value_store, resolve_str(symbol)).as_str(),
    );
  }

  for symbol_value in definitions.iter() {
    log(Channel::Debug, 4, "Value found: ");
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
    log(Channel::Debug, 4, format!("pattern = {}", (*pattern).to_string()).as_str());
    let mut matcher = Matcher::new(pattern.clone(), ground.clone(), context);
    if let Some(substitutions) = (&mut matcher).next() {
      log(Channel::Debug, 4, format!("Pattern matched!").as_str());
      return Some((symbol_value.clone(), substitutions));
    } else {
      log(Channel::Debug, 4, format!("Pattern failed to matched.").as_str());
    }
  } // end iterate over definitions
  None
}


/// Performs all substitutions in the given solution set on expression.
pub fn replace_all_bound_variables(expression: Atom, substitutions: &SolutionSet, context: &mut Context) -> Atom {
  match &expression {

    Atom::SExpression(children) => {

      // Do a `ReplaceAll` on the children
      let new_children =
          children.iter()
                  .map(|c| replace_all_bound_variables(c.clone(), substitutions, context))
                  .collect();

      Atom::SExpression(Rc::new(new_children))
    }

    Atom::Symbol(name) => {
      // If `expression` itself matches a key in `substitutions`, replace it. This is the base case for the recursion.
      for (pattern, substitution) in substitutions {
        let pattern_name = pattern.is_variable().expect("Nonvariable pattern in a variable binding.");
        if pattern_name == *name {
          return substitution.clone();
        }
      }
      // None apply.
      expression
    }

    _ => expression
  }
}

/// Threads `N` over functions while respecting any `NHold*` attributes.
#[allow(non_snake_case)]
pub fn propogate_N(expression: Atom, context: &mut Context) -> Atom {
  let child = &SExpression::children(&expression)[1];
  // If child isn't an SExpression, it doesn't have an `NHold*` attribute.
  let grandchildren = match child.is_function() {
    Some(c) => c,
    None => {
      return expression;
    }
  };

  match grandchildren[0] {
    Atom::Symbol(name) => {
      /// Fetch attributes and check for NHold*.
      let attributes = context.get_attributes(name);

      let new_children = // the result of this if
        if attributes[Attribute::NHoldAll] {
          return child.clone();
        }
        else if attributes[Attribute::NHoldFirst] {
          let mut c = vec![grandchildren[0].clone(), grandchildren[1].clone()];

          c.extend(grandchildren[2..].iter().map(|e|
              propogate_N(
                SExpression::new(expression.head(), vec![e.clone()]),
                context
              )
          ));
          c
        }
        else if attributes[Attribute::NHoldRest] {
          let mut c: Vec<Atom> = grandchildren[..2].iter().map(|e| {
            propogate_N(
              SExpression::new(expression.head(), vec![e.clone()]),
              context
            )
          }).collect();
          c.extend(grandchildren[2..].iter().cloned());
          c
        }
        else { // Hold none
          grandchildren.iter().map(|e| {
            propogate_N(
              SExpression::new(expression.head(), vec![e.clone()]),
              context
            )
          }).collect()
        };

      Atom::SExpression(Rc::new(new_children))
    }

    _ => {
      // The head is not a symbol, so apply N to everything.
      let new_children = grandchildren.iter().map(|e|
          propogate_N(
            SExpression::new(expression.head(), vec![e.clone()]),
            context
          )
      ).collect();
      Atom::SExpression(Rc::new(new_children))
    }

  } // match on head of grandchildren
}


/// Threads `Listable` functions, evaluates the `OneIdentity` property. Note that these two attributes are
/// mutually exclusive.
pub fn propogate_attributes(expression: Atom, context: &mut Context) -> Atom {
  // todo: This code is… ugly. Nothing wrong with it, but… ugly.
  match &expression {

    Atom::SExpression(children) => {
      let outer_head = children[0].clone();
      // N is a special case because its child can have NHoldAll, NHoldRest, or NHoldFirst
      if outer_head == Symbol::from_static_str("N"){
        return propogate_N(expression, context);
      }
      let record = context.get_symbol_mut(outer_head.name().unwrap());

      if record.attributes.listable() && children.len() == 2 {
        match &children[1] {
          Atom::SExpression(inner_children) => {

            let new_children = inner_children[1..].iter()
                                                 .map(|e| {
                                                   // apply outer_head to e and recurse.
                                                   propogate_attributes(
                                                     Atom::SExpression(Rc::new(
                                                       vec![outer_head.clone(), e.clone()]
                                                     )),
                                                     context
                                                   )
                                                 })
                                                 .collect::<Vec<_>>();
            SExpression::new(inner_children[0].clone(), new_children)
          } // end match to function

          _ => expression
        } // end match on only child.
      } // end if listable
      // OneIdentity
      else if record.attributes.one_identity() && children.len()==2 {
        propogate_attributes(children[1].clone(), context)
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
  use crate::parsing::parse;
  use super::*;

  #[test]
  fn eval_built_in_N() {
    let unevaluated = parse("N[2]").unwrap();
    let expected = parse("2.0").unwrap();
    let mut root_context = Context::new_global_context();

    let evaluated = evaluate(unevaluated, &mut root_context);

    assert_eq!(evaluated, expected);
  }
}

