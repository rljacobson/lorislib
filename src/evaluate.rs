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
use std::iter::Peekable;
use std::ops::Deref;
use regex::internal::Input;

use crate::{
  matching::{
    SolutionSet,
    Matcher,
    display_solutions,
    self
  },
  context::{
    SymbolValue,
    Context,
    ContextValueStore
  },
  atom::{
    Symbol,
    SExpression,
    Atom
  },
  logging::{
    log,
    Channel
  },
  attributes::Attribute,
  interner::{
    InternedString,
    resolve_str
  }
};
use crate::built_ins::{BuiltinFn, BuiltinFnMut};

enum UnevaluatedDefinitionMatch{
  None,
  /// To be passed to `replace_all_bound_variables(…)`
  Definition{
    rhs: Atom,
    substitutions: SolutionSet
  },
  // To be applied to the expression argument to `find_matching_definition`
  BuiltIn{
    substitutions: SolutionSet,
    built_in: BuiltinFn
  },
  // To be applied to the expression argument to `find_matching_definition`
  BuiltInMut{
    substitutions: SolutionSet,
    built_in: BuiltinFnMut
  }
}

impl UnevaluatedDefinitionMatch{
  pub fn is_none(&self) -> bool {
    match *self {
      UnevaluatedDefinitionMatch::None => true,
      _ => false,
    }
  }

  pub fn is_some(&self) -> bool {
    !self.is_none()
  }

  pub fn is_safe(&self) -> bool {
    match self {
      | UnevaluatedDefinitionMatch::None{..}
      | UnevaluatedDefinitionMatch::BuiltInMut{..} => false,

      _ => true
    }
  }
/*
  // todo: factor out common code with regular apply
  pub fn safe_apply(self, expression: Atom, context: &Context) -> Atom {
    match self {

      UnevaluatedDefinitionMatch::None => { unreachable!("Called evaluate on a non-expression.") }

      UnevaluatedDefinitionMatch::Definition { rhs, substitutions } => {
        match replace_all_bound_variables(&rhs, &substitutions, context) {
          None => {
            rhs
          }
          Some(e) => {
            e
          }
        }
      }

      UnevaluatedDefinitionMatch::BuiltIn { substitutions, built_in } => {
        built_in(substitutions, expression, context)
      }

      UnevaluatedDefinitionMatch::BuiltInMut { substitutions, built_in } => {
        // Not necessarily an error.
        // log(Channel::Error, 1, "Tried to safely evaluate an unsafe expression.");
        Symbol::from_static_str("Null")
      }

    }
  }
*/
  pub fn apply(self, expression: Atom, context: &mut Context) -> Atom {
    match self {

      UnevaluatedDefinitionMatch::None => { unreachable!("Called evaluate on a non-expression. This is a bug.") }

      UnevaluatedDefinitionMatch::Definition { rhs, substitutions } => {
        match replace_all_bound_variables(&rhs, &substitutions, context) {
          None => {
            rhs
          }
          Some(e) => {
            e
          }
        }
      }

      UnevaluatedDefinitionMatch::BuiltIn { substitutions, built_in } => {
        built_in(substitutions, expression, context)
      }

      UnevaluatedDefinitionMatch::BuiltInMut { substitutions, built_in } => {
        built_in(substitutions, expression, context)
      }

    }
  }
}
/*
// todo: factor out common  code with normal evaluate.
/// Evaluates `expression` without mutating `context`.
pub fn safe_evaluate(expression: Atom, context: &Context) -> Atom {
  /*
  The general strategy is to apply an operation to an expression, see if it has changed, and if it has, to evaluate
  again, until the expression reaches a fixed-point.

  Todo: Add recursion-limit
  Todo: Add cycle detection

  */

  let expression = propagate_attributes(&expression, context);

  // This function assumes the caller has already taken care of any `UpValues`.
  // Numbers and variables evaluate to themselves. It suffices to only take care
  // of the `Symbol` and `Function` cases.
  match &expression {

    Atom::Symbol(symbol) => {
      // Look for OwnValues.
      // log(Channel::Debug, 4, "Evaluating symbol. Checking for own-values.");

      let original_hash = expression.hashed();
      let unevaluated = find_matching_definition(
        expression.clone(),
        *symbol,
        ContextValueStore::OwnValues,
        context
      );
      if unevaluated.is_safe() {
        let exp = unevaluated.safe_apply(expression, context);
        if exp.hashed() != original_hash{
          // Something has changed, so continue evaluating.
          safe_evaluate(exp, context)
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
                    Attribute::HoldFirst
                  } else if attributes[Attribute::HoldRest]
                      && children.len() > 2 // There needs to be a "rest" to hold.
                  {
                    Attribute::HoldRest
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
              let unevaluated = evaluate_up_values(&expression, &children[2..], context);
              if unevaluated.is_safe() {
                unevaluated.safe_apply(expression, context)
              }
              // No applicable up-values.
              // Step 2: Evaluate children.
              else {
                let mut evaluated_children = Vec::with_capacity(children.len());
                evaluated_children.push(children[0].clone()); // This is expression.head()
                evaluated_children.push(children[1].clone()); // ...and the first child
                evaluated_children.extend(
                  children[2..].iter().cloned().map(|exp| safe_evaluate(exp, context))
                );
                Atom::SExpression(Rc::new(evaluated_children))
              }
            } // end HoldFirst branch

            Some((_name, Attribute::HoldRest)) => {
              // Step 1: Look for `UpValues` for each unheld child.
              // For UpValues, we match on the parent instead of the child expression that is associated with the up-value.
              // log(Channel::Debug, 4, "Evaluating function. Checking for up-values.");
              let unevaluated = evaluate_up_values(&expression, &children[1..2], context);
              if unevaluated.is_safe() {
                unevaluated.safe_apply(expression, context)
              }
              // No applicable up-values.
              // Step 2: Evaluate children.
              else {
                let mut evaluated_children = Vec::with_capacity(children.len());
                evaluated_children.push(safe_evaluate(children[0].clone(), context)); // This is expression.head()
                evaluated_children.push(safe_evaluate(children[1].clone(), context)); // ...and the first child
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
              let unevaluated = evaluate_up_values(&expression, &children[1..], context);
              if unevaluated.is_safe() {
                unevaluated.safe_apply(expression, context)
              }
              // No applicable up-values.
              // Step 2: Evaluate children.
              else {
                let evaluated_children
                    = children.iter()
                              .map(|child| safe_evaluate(child.clone(), context))
                              .collect::<Vec<_>>();
                Atom::SExpression(Rc::new(evaluated_children))
              }
            } // end None branch

          }; // end match on name_and_hold_attribute

      // If steps 1 or 2 were successful, then we changed the expression somehow.
      if new_expression.hashed() != original_hash {
        log(
          Channel::Debug,
          4,
          "Evaluating up-values and children changed the expression. Evaluating again."
        );
        // We have changed the expression or the context somehow, which
        // might affect the application of UpValues. Abort this evaluation in favor of evaluation of the new function.
        return safe_evaluate(new_expression, context);
      }

      // Step 3: Evaluate DownValues.
      // We can only have down-values if the head has a name.
      if let Some((name, _)) = name_and_hold_attribute {
        log(Channel::Debug, 4, "Looking for down values.");
        let unevaluated = find_matching_definition(
          new_expression.clone(),
          name,
          ContextValueStore::DownValues,
          context
        );
        if unevaluated.is_safe(){
          let new_expression = unevaluated.safe_apply(new_expression, context);
          if original_hash != new_expression.hashed()
          {
            log(
              Channel::Debug,
              4,
              "Evaluating DownValue changed the expression. Evaluating again."
            );
            safe_evaluate(new_expression, context)
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
*/

pub fn evaluate(expression: Atom, context: &mut Context) -> Atom {
  /*
  The general strategy is to apply an operation to an expression, see if it has changed, and if it has, to evaluate
  again, until the expression reaches a fixed-point.

  Todo: Add recursion-limit
  Todo: Add cycle detection

  Todo: If a grandparent has attribute SequenceHold, for example, that affects how the expression is evaluated. This
        problem also exists for evaluating `N` (with NHold), but we solved that by giving it its own evaluation
        function. Instead, we need an Evaluator that holds state across calls to evaluate, just like we do with
        `Formattable`/`ExpressionFormatter`. So far it would just hold and `Attributes`, but...maybe it holds the
        context.

  */

  let expression = propagate_attributes(&expression, context);

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

      let unevaluated = find_matching_definition(
        expression.clone(),
        *symbol,
        ContextValueStore::OwnValues,
        context
      ) ;
      if unevaluated.is_some() {
        let exp = unevaluated.apply(expression, context);

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
                    Attribute::HoldFirst
                  } else if attributes[Attribute::HoldRest]
                      && children.len() > 2 // There needs to be a "rest" to hold.
                  {
                    Attribute::HoldRest
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
            let new_expression  = evaluate_up_values(&expression, &children[2..], context);
            if new_expression.is_some() {
              new_expression.apply(expression, context)
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
            let unevaluated = evaluate_up_values(&expression, &children[1..2], context);
            if unevaluated.is_some() {
              unevaluated.apply(expression, context)
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
            // The silliest case: We cannot evaluate any of the children.
            expression
          }

          _ => {
            // No restrictions – evaluate everything
            // Step 1: Look for `UpValues` for each unheld child.
            // For UpValues, we match on the parent instead of the child expression that is associated with the up-value.
            // log(Channel::Debug, 4, "Evaluating function. Checking for up-values.");
            let unevaluated = evaluate_up_values(&expression, &children[1..], context);
            if unevaluated.is_some() {
              unevaluated.apply(expression, context)
            }
            // No applicable up-values.
            // Step 2: Evaluate children.
            else {
              let evaluated_children
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
        let unevaluated = find_matching_definition(
          new_expression.clone(),
          name,
          ContextValueStore::DownValues,
          context
        );
        if unevaluated.is_some()  {
          let new_expression = unevaluated.apply(new_expression, context);
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
fn evaluate_up_values(expression: &Atom, children: &[Atom], context: &mut Context) -> UnevaluatedDefinitionMatch {
  for child in children.iter() {
    if let Some(name) = child.name() {
      let unevaluated_match = find_matching_definition(expression.clone(), name, ContextValueStore::UpValues, context);
      if unevaluated_match.is_some() {
        // An up-value modifies this parent expression, so if a single up-value applies, return the new modified
        // expression.
        return unevaluated_match;
      }
    }
  }
  UnevaluatedDefinitionMatch::None
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
  log(Channel::Debug, 4, format!("Checking condition expression: {}\n  with substitutions: {}",
                                 condition, display_solutions(substitutions)).as_str());
  let condition_expression = match replace_all_bound_variables(&condition, substitutions, context) {
    Some(expression) => expression,
    None => condition
  };
  log(Channel::Debug, 4, format!("Evaluating condition expression: {}", condition_expression).as_str());
  let condition_result = evaluate(condition_expression, context);
  condition_result.is_true()
}

// Returns pair (&SymbolValue, Atom) if a definition pattern matches AND any required conditions are met.
fn wrap_definition_match(symbol_value: &SymbolValue, substitutions: SolutionSet) -> UnevaluatedDefinitionMatch
{
  match &symbol_value {
    SymbolValue::Definitions { rhs, .. } => {
      return UnevaluatedDefinitionMatch::Definition { rhs: rhs.clone(), substitutions }
    }

    SymbolValue::BuiltIn {built_in, .. } =>{
      log(
        Channel::Debug,
        4,
        "Found BuiltIn",
      );
      return UnevaluatedDefinitionMatch::BuiltIn{
        substitutions,
        built_in: *built_in
      }
    }


    SymbolValue::BuiltInMut {condition, built_in, .. } => {
      log(
        Channel::Debug,
        4,
        "Found BuiltIn",
      );
      return UnevaluatedDefinitionMatch::BuiltInMut{
        substitutions,
        built_in: *built_in
      };
    }

    // _ => UnevaluatedDefinitionMatch::None
  }
}

/// If any of the patterns in the vector of ``SymbolValue``'s match, return the RHS and the substitutions for the match.
fn find_matching_definition(ground: Atom, symbol: InternedString, value_store: ContextValueStore, context: &mut Context)
    -> UnevaluatedDefinitionMatch
{
  let definitions = {
    if let Some(record) = context.get_symbol(symbol) {
      match value_store {
        ContextValueStore::OwnValues => &record.own_values,
        ContextValueStore::UpValues => &record.up_values,
        ContextValueStore::DownValues => &record.down_values,
        ContextValueStore::SubValues => &record.sub_values,
        _ => unimplemented!()
        // ContextValueStore::NValues => {}
        // ContextValueStore::DisplayFunction => {}
      }
    } else {
      // None to try
      return UnevaluatedDefinitionMatch::None;
    }
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
    let (pattern, condition) =
        match symbol_value {

          SymbolValue::Definitions{lhs, condition,..}=> {
            (lhs, condition)
          }

          | SymbolValue::BuiltIn {pattern, condition, ..}
          | SymbolValue::BuiltInMut {pattern, condition, ..} => {
            (pattern, condition)
          }

        };

    log(Channel::Debug, 4, format!("pattern = {}", (pattern).to_string()).as_str());

    let matches: Vec<SolutionSet> = Matcher::new(pattern.clone(), ground.clone(), context).collect();

    for substitutions in matches {
      if let Some(c) = condition{
        if check_condition(c.clone(), &substitutions, context) {
          // matched_set.push((&symbol_value, substitutions));
          log(Channel::Debug, 4, format!("Pattern matched! Condition satisfied!").as_str());
          return wrap_definition_match(symbol_value, substitutions);
        } else {
          log(Channel::Debug, 4, format!("Condition failed,").as_str());
        }
      } else {
        // No condition needs satisfying
        return wrap_definition_match(symbol_value, substitutions);
      }
    } // end iterate over substitutions
  } // end iterate over definitions

  log(Channel::Debug, 4, format!("Pattern failed to matched while satisfying condition.").as_str());

  UnevaluatedDefinitionMatch::None
}


/// Performs all substitutions in the given solution set on expression.
pub fn replace_all_bound_variables(expression: &Atom, substitutions: &SolutionSet, context: &Context)
  -> Option<Atom>
{
  match &expression {

    Atom::SExpression(children) => {

      // Do a `ReplaceAll` on the children
      let new_children =
          children.iter()
                  .map(|c| {
                    match replace_all_bound_variables(c, substitutions, context) {
                      Some(e) => e,
                      None => c.clone()
                    }
                  })
                  .collect();

      Some(Atom::SExpression(Rc::new(new_children)))
    }

    Atom::Symbol(name) => {
      // If `expression` itself matches a key in `substitutions`, replace it. This is the base case for the recursion.
      for (pattern, substitution) in substitutions {
        if let Some(pattern_name) = pattern.is_variable() {
          if pattern_name == *name {
            return Some(substitution.clone());
          }
        }
        else if let Some(pattern_name) = pattern.is_null_sequence_variable() {
          if pattern_name == *name {
            return Some(substitution.clone());
          }
        }
        else if let Some(pattern_name) = pattern.is_sequence_variable() {
          if pattern_name == *name {
            return Some(substitution.clone());
          }
        }

        // unreachable!("Nonvariable pattern in a variable binding: {} -> {}", pattern_name, *name);
      }
      // None apply.
      None
    }

    _ => None
  }
}

/// Threads `N` over functions while respecting any `NHold*` attributes.
#[allow(non_snake_case)]
pub fn propagate_N(expression: Atom, context: &mut Context) -> Atom {
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
      // Fetch attributes and check for NHold*.
      let attributes = context.get_attributes(name);

      let new_children = // the result of this if
        if attributes[Attribute::NHoldAll] {
          return child.clone();
        }
        else if attributes[Attribute::NHoldFirst] {
          let mut c = vec![grandchildren[0].clone(), grandchildren[1].clone()];

          c.extend(grandchildren[2..].iter().map(|e|
              propagate_N(
                SExpression::new(expression.head(), vec![e.clone()]),
                context
              )
          ));
          c
        }
        else if attributes[Attribute::NHoldRest] {
          let mut c: Vec<Atom> = grandchildren[..2].iter().map(|e| {
            propagate_N(
              SExpression::new(expression.head(), vec![e.clone()]),
              context
            )
          }).collect();
          c.extend(grandchildren[2..].iter().cloned());
          c
        }
        else { // Hold none
          grandchildren.iter().map(|e| {
            propagate_N(
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
          propagate_N(
            SExpression::new(expression.head(), vec![e.clone()]),
            context
          )
      ).collect();
      Atom::SExpression(Rc::new(new_children))
    }

  } // match on head of grandchildren
}


/// Threads `Listable` functions, evaluates the `OneIdentity` property, flattens associative functions.. Note that
/// `OneIdentity` and `Associative` are individually mutually exclusive with `Listable`.
pub fn propagate_attributes(expression: &Atom, context: &mut Context) -> Atom {
  // todo: This code is… ugly. Nothing wrong with it, but… ugly.
  match expression {

    Atom::SExpression(children) => {
      let outer_head = children[0].clone();
      // N is a special case because its child can have NHoldAll, NHoldRest, or NHoldFirst
      if outer_head == Symbol::from_static_str("N"){
        return propagate_N(expression.clone(), context);
      }
      let attributes = context.get_attributes(outer_head.name().unwrap());

      if attributes.listable() && children.len() == 2 {
        match &children[1] {
          Atom::SExpression(inner_children) => {

            let new_children = inner_children[1..].iter()
                                                 .map(|e| {
                                                   // apply outer_head to e and recurse.
                                                   propagate_attributes(
                                                     &Atom::SExpression(Rc::new(
                                                       vec![outer_head.clone(), e.clone()]
                                                     )),
                                                     context
                                                   )
                                                 })
                                                 .collect::<Vec<_>>();
            SExpression::new(inner_children[0].clone(), new_children)
          } // end match to function

          _ => expression.clone()
        } // end match on only child.
      } // end if listable
      // OneIdentity
      else if attributes.one_identity() && children.len()==2 {
        propagate_attributes(&children[1], context)

      }
      // "Flat", i.e. associative
      else if attributes.associative() {
        // Todo: This is terribly inefficient. Every associative function gets completely recreated on every call to
        //       evaluate.
        // Visit in post order.
        let mut new_children = vec![children[0].clone()];
        for child in &children[1..] {
          let new_child = propagate_attributes(&child, context);
          if let Some(grandchildren) = new_child.is_function() {
            // if (head of child) == (head of expression) …
            if grandchildren[0] == children[0]{
              // splice
              new_children.extend(grandchildren[1..].iter().cloned());
              } else {
              // splice
              new_children.push(new_child);
            }
          } else {
            new_children.push(new_child);
          }
        }

        Atom::SExpression(Rc::new(new_children))
      }
      // No special attributes
      else {
        Atom::SExpression(Rc::new(children.iter().map(|a| propagate_attributes(a, context)).collect()))
      }

    }

    _ => expression.clone()
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

