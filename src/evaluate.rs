/*!

Facilities for evaluating expressions within a context.

Evaluating an instance of `Replace` or `ReplaceAll` is equivalent to evaluating with a Context that is empty except
for the `own_values` the replacements represent.

`*Set` evaluates its RHS at definition time, while `*SetDelayed` evaluates its RHS at substitution time. All are
stored in the form `RuleDelayed[ HoldPattern[ lhs ], rhs ]`

Todo: implement scoping.

 */

use std::{
  iter,
  rc::Rc
};
use crate::{
  context::SymbolValue,
  atoms::{Atom, Function, Symbol},
  Context,
  Expression,
  RcExpression,
  matching::{Matcher, SolutionSet},
  logging::{log, Channel}
};

/// Evaluates `expression` in `context`.
pub fn evaluate(expression: RcExpression, context: &mut Context) -> RcExpression {
  // This function assumes the caller has already taken care of any `up_values`.
  // Numbers and variables evaluate to themselves, and sequences should not exist (except possibly as the sequence
  // function `Sequence[…]`). It suffices to only take care of the `Symbol` and `Function` cases.
  let original_hash = expression.hash();

  match expression.as_ref() {
    | Expression::Sequence(_)
    | Expression::Variable(_)
    | Expression::SequenceVariable(_)
    | Expression::StringLiteral(_)
    | Expression::Integer(_)
    | Expression::Real(_) => { expression }

    Expression::Symbol(symbol) => {
      // Look for own_values.
      if let Some(own_values) = context.get_own_values(expression.name().as_str()) {
        if let Some(exp) = try_definitions(expression.clone(), &own_values, context) {
          return exp;
        }
      }
      return expression;
    }

    Expression::Function(function) => {
      // Step 1: Look for `up_values` for each child.
      // For up_values, we match on the parent instead of the expression itself.
      log(Channel::Debug, 5, "Evaluating function. Checking for upvalues.");
      for child in function.children.iter() {
        if let Some(up_values) = context.get_up_values(child.name().as_str()) {
          if let Some(exp) = try_definitions(expression.clone(), &up_values, context) {
            return exp;
          }
        }
      }

      // Step 2: Evaluate all children.
      log(Channel::Debug, 5, "Evaluating children.");
      let mut f = function.duplicate_head();
      f.children = function.children.iter().map(|child| evaluate(child.clone(), context)).collect();
      if original_hash != f.hash() {
        // We have changed the expression somehow, which might affect the application of up_values. Abort this
        // evaluation in favor of evaluation of the new function.
        return evaluate(Rc::new(f.into()), context);
      }

      // Step 3: Evaluate down_values
      log(Channel::Debug, 5, "Looking for down values.");
      let symbol_record = context.get_symbol(expression.name().as_str());
      if !symbol_record.down_values.is_empty() {
        log(Channel::Debug, 5, "Found down values.");
        // todo: Get rid of this copy.
        let down_values = symbol_record.down_values.clone();
        if let Some(exp) = try_definitions(expression.clone(), &down_values, context) {
          return exp;
        }
      }

      // Step 4: Done?
      return expression;

    } // end Expression::Function arm.
  } // end match on Expression enum.

  // Ok(new_expression)
} // end evaluate.

/**
Evaluating rules with conditions is a bit meta, because evaluation is
defined in terms of evaluation. That is, to evalaute a rule, one must first
evaluate the condition. To break the infinite regress, most rules do not have
conditions, and most conditions are either simple or do not themselves have
conditions.
*/
fn check_condition(condition: RcExpression, substitutions: &SolutionSet, context: &mut Context)
    -> bool
{
  let condition_expression = replace_all(condition, substitutions);
  let condition_result = evaluate(condition_expression, context);
  condition_result.name() == "True"
}

fn try_definitions(expression: RcExpression, definitions: &Vec<SymbolValue>, context: &mut Context)
  -> Option<RcExpression>
{
  if let Some((symbol_value, substitutions)) = find_matching_definition(expression.clone(), definitions){
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
fn find_matching_definition(ground: RcExpression, definitions: &Vec<SymbolValue>)
  -> Option<(&SymbolValue, SolutionSet)> {
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
    log(Channel::Debug, 5, format!("pattern = {}", pattern).as_str());
    let mut matcher = Matcher::new(pattern.clone(), ground.clone());
    if let Some(substitutions) = (&mut matcher).next() {
      log(Channel::Debug, 5, format!("Pattern matched!").as_str());
      return Some((symbol_value, substitutions));
    }
  } // end iterate over definitions
  None
}


/// Performs all substitutions in the given solution set on expression.
pub fn replace_all(expression: RcExpression, substitutions: &SolutionSet) -> RcExpression {
  match expression.as_ref() {

    | Expression::Variable(_)
    | Expression::SequenceVariable(_) => {
      match substitutions.get(expression.as_ref()) {
        Some(e) => e.clone(),
        None    => expression
      }
    },

    Expression::Function(function) => {
      // Do a `ReplaceAll` on the children
      let head = replace_all(function.head.clone(), substitutions);
      // Do a `ReplaceAll` on the children
      let children = function.children.iter().map(|c| replace_all(c.clone(), substitutions)).collect();
      Rc::new(Function{
        head,
        children,
        attributes: function.attributes,
        .. Function::default()
      }.into())
    }

    _ => {
      expression
    }
  }
}


pub fn apply(function: RcExpression, expression: RcExpression) -> RcExpression {
  let mut f = Function::new(function);
  f.children.push(expression);
  Rc::new(f.into())
}

/// Threads `Listable` functions, evaluates the `OneIdentity` property. Note that these two attributes cannot be set
/// simultaneously.
pub fn propogate_attributes(expression: RcExpression, context: &mut Context) -> RcExpression {
  match expression.as_ref() {

    Expression::Function(function) => {
      let record = context.get_symbol(expression.name());

      if record.attributes.listable() && function.children.len()==1{
        match function.children.first().unwrap().as_ref() {
          Expression::Function(inner_function) => {

            let mut f = inner_function.duplicate_head();
            f.children = inner_function.children
                .iter()
                .map(|e| {
                  // apply function.head to e.
                  propogate_attributes(apply(function.head.clone(), e.clone()), context)
                }).collect();
            return Rc::new(f.into());
          } // end match to function

          _other => { return expression; }
        } // end match on only child.
      } // end if listable

      if record.attributes.one_identity() && function.children.len()==1 {
        return propogate_attributes(function.children.first().unwrap().clone(), context);
      }

      expression
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

