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

/// Evaluates `expression` in `context`.
pub fn evaluate(expression: Atom, context: &mut Context) -> Atom {
  /*
  The general strategy is to apply an operation to an expression, see if it has changed, and if it has, to evaluate
  again, until the expression reaches a fixed-point.

  Todo: Add recursion-limit
  Todo: Add cycle detection

  */

  if let Atom::SExpression(children) = &expression {
    let attrs: Attributes = context.get_attributes(children[0].name().unwrap());
    if attrs[Attribute::HoldAll] || attrs[Attribute::HoldAllComplete] {
      return expression;
    }
  }


  // This function assumes the caller has already taken care of any `UpValues`.
  // Numbers and variables evaluate to themselves. It suffices to only take care
  // of the `Symbol` and `Function` cases.
  let original_hash = expression.hashed();
  // The "state version" of `context` that this expression was last evaluated at.
  let evaluated_version = context.state_version();

  match &expression {
    Atom::Symbol(symbol) => {
      // Look for OwnValues.
      // log(Channel::Debug, 4, "Evaluating symbol. Checking for own-values.");

      if let Some(exp) = try_definitions(
        expression.clone(),
        *symbol,
        ContextValueStore::OwnValues,
        context
      ) {
        return if exp.hashed()!=original_hash || evaluated_version != context.state_version() {
          evaluate(exp, context)
        } else {
          exp
        }
      }
      expression
    }

    Atom::SExpression(children) => {
      log(
        Channel::Debug,
        4,
        format!(
          "Evaluating {}",
          &expression
        ).as_str()
      );


      // Step 0: Propagate attributes to children.
      let propogated = propogate_attributes(expression.clone(), context);
      if propogated.hashed() != original_hash{
        log(
          Channel::Debug,
          4,
          "Propagating attributes changed the expression. Evaluating again."
        );
        // Changed, redo evaluation.
        return evaluate(propogated, context);
      }

      // Step 1: Look for `UpValues` for each child.
      // For UpValues, we match on the parent instead of the expression itself.
      // log(Channel::Debug, 4, "Evaluating function. Checking for upvalues.");

      for child in children[1..].iter() {
        if let Some(name) = child.name() {
          if let Some(exp) = try_definitions(expression.clone(), name, ContextValueStore::UpValues, context) {
            // todo: Return here or..?
            // An up-value modifies this parent expression, so if a single up-value applies, return the new modified
            // expression.
            return if exp.hashed() != original_hash || evaluated_version != context.state_version() {
              evaluate(exp, context)
            } else {
              exp
            }
          }
        }
      }

      // Step 2: Evaluate children.
      log(Channel::Debug, 4, "Evaluating children.");

      // Todo: make work with functions with non-symbol heads.
      // Which children are evaluated depends on the Hold* attributes of the function.
      let new_children =  // the following match
          match expression.name() {

            Some(name)
            => {
              let attributes = context.get_attributes(name);

              if attributes[Attribute::HoldRest] && expression.len()>1 {
                let mut c = vec![
                  evaluate(children[0].clone(), context),
                  evaluate(children[1].clone(), context),
                ];
                c.extend(children[2..].iter().cloned());
                c
              }
              else if attributes[Attribute::HoldFirst] && expression.len() > 0 {
                let mut c = vec![
                  children[0].clone(),
                  children[1].clone(),
                ];
                c.extend(children[2..].iter().cloned().map(|exp| evaluate(exp, context)));
                c
              } else if attributes[Attribute::HoldAll] {
                children.to_vec()
              } else {
                children.iter().map(|child| evaluate(child.clone(), context)).collect::<Vec<_>>()
              }
            }

            _ => {
              children.iter().map(|child| evaluate(child.clone(), context)).collect::<Vec<_>>()
            }

          }; // end match on which children to evaluate

      let f = Atom::SExpression(Rc::new(new_children));
      if original_hash != f.hashed() || evaluated_version != context.state_version() {
        log(
          Channel::Debug,
          4,
          format!(
            "original hash: {} new hash:{} original eval version: {} new eval version: {}",
            original_hash,
            f.hashed(),
            evaluated_version,
            context.state_version()
          ).as_str()
        );
        log(
          Channel::Debug,
          4,
          "Evaluating children changed the expression. Evaluating again."
        );
        // We have changed the expression or the context somehow, which
        // might affect the application of UpValues. Abort this evaluation in favor of evaluation of the new function.
        return evaluate(f, context);
      }

      // Step 3: Evaluate DownValues
      log(Channel::Debug, 4, "Looking for down values.");
      if let Some(name) = expression.name() {
        if let Some(exp) = try_definitions(
          expression.clone(),
          name,
          ContextValueStore::DownValues,
          context
        ) {
          return if evaluated_version != context.state_version() || original_hash != exp.hashed() {
            log(
              Channel::Debug,
              4,
              "Evaluating DownValue changed the expression. Evaluating again."
            );
            evaluate(exp, context)
          } else {
            log(
              Channel::Debug,
              4,
              "Evaluating DownValue left expression unchanged. Returning."
            );
            exp
          }
        } else {
          log(
            Channel::Debug,
            4,
            "Down-values didn't match. Aborting evaluation."
          );
          expression
        }
      } else {
        log(
          Channel::Debug,
          4,
          "Head has no name. Aborting evaluation."
        );
        expression
      }

      // Step 4: Done?
    } // end Atom::SExpression arm.

    _any_other_expression => expression
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

