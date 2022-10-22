/*!

Expression manipulation

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
use crate::built_ins::{occurs_check, register_builtin};
#[allow(unused_imports)]#[allow(unused_imports)]
use crate::interner::resolve_str;
#[allow(unused_imports)]
use crate::logging::set_verbosity;




/// Implements calls matching
///     `Occurs[needle_, haystack_] := built-in[needle, haystack]`
pub fn Occurs(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Occurs called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );
  let needle   = &arguments[&SExpression::variable_static_str("needle")];
  let haystack = &arguments[&SExpression::variable_static_str("haystack")];

  if occurs_check(&needle, &haystack) {
    Symbol::from_static_str("True")
  } else {
    Symbol::from_static_str("False")
  }
}


/// Internal version of `ReplaceAll`
/// Performs all substitutions in the given solution set on expression.
pub fn replace_all(expression: Atom, substitutions: &SolutionSet, context: &mut Context) -> Atom {
  // If `expression` itself matches a key in `substitutions`, replace it. This is the base case for the recursion.
  for (pattern, substitution) in substitutions {
    let mut matcher = Matcher::new(pattern.clone(), expression.clone(), context);
    match matcher.next() {
      Some(_) => {
        return substitution.clone()
      }
      None => {
        continue;
      }
    }
  }

  match &expression {

    Atom::SExpression(children) => {

      // Do a `ReplaceAll` on the children
      let new_children =
          children.iter()
                  .map(|c| replace_all(c.clone(), substitutions, context))
                  .collect();

      Atom::SExpression(Rc::new(new_children))
    }

    _ => expression
  }
}


/// ReplaceAll[exp_, rules_]
/// Given a list of rules, performs all substitutions defined by the rules at once.
pub fn ReplaceAll(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Replace called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  let expression = &arguments[&SExpression::variable_static_str("exp")];
  let rules_expression = &arguments[&SExpression::variable_static_str("rules")];

  let rules: SolutionSet = // the following match
      match rules_expression {

        // Three cases: A list of rules, or a single rule, or invalid input.
        Atom::SExpression(children) => {
          // List of rules
          if children[0] == Atom::Symbol(interned_static("List")) {
            // Now validate each element of the list.
            let rule_list: Vec<(Atom, Atom)> = children[1..].iter().map_while(|r| r.is_rule()).collect::<Vec<_>>();

            if rule_list.len() != children.len() -1 {
              // Not all calls to `is_rule()` returned Some(…)
              log(Channel::Error, 1, "Invalid input provided to Replace.");
              return original;
            }

            // Internally, a set of rules is a hashmap.
            HashMap::from_iter(rule_list.into_iter())
          }

          // Single Rule
          else if let Some((lhs, rhs)) = expression.is_rule() {
            // Internally a rule is a hashmap entry.
            HashMap::from([(lhs, rhs)])
          }

          // Invalid input.
          else {
            log(Channel::Error, 1, "Invalid input provided to Replace.");
            return original;
          }
        }

        // Not even an S-expression.
        _ => {
          log(Channel::Error, 1, "Invalid input provided to Replace.");
          return original;
        }

      }; // end match on rule_expression

  // Apply all rules at once.
  replace_all(expression.clone(), &rules, context)

}

/// Replace[exp_, rules_]
/// A list of rules are given. The rules are tried in order. The result of the first one that applies is returned.
/// If none of the rules apply, the original expr is returned.
pub fn Replace(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Replace called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  let expression = &arguments[&SExpression::variable_static_str("exp")];
  let rules_expression = &arguments[&SExpression::variable_static_str("rules")];

  let rules: Vec<SolutionSet> = // the following match
      match rules_expression {

        // Three cases: A list of rules, or a single rule, or invalid input.
        Atom::SExpression(children) => {
          // List of rules
          if children[0] == Atom::Symbol(interned_static("List")) {
            // Now validate each element of the list.
            let rule_list = children[1..].iter().map_while(|r| r.is_rule()).collect::<Vec<_>>();

            if rule_list.len() != children.len() -1 {
              // Not all calls to `is_rule()` returned Some(…)
              log(Channel::Error, 1, "Invalid input provided to Replace.");
              return original;
            }

            // Internally, a rule is a hashmap entry.
            rule_list.into_iter().map(|r| HashMap::from([r])).collect::<Vec<_>>()
          }

          // Single Rule
          else if let Some((lhs, rhs)) = expression.is_rule() {
            vec![HashMap::from([(lhs, rhs)])]
          }

          // Invalid input.
          else {
            log(Channel::Error, 1, "Invalid input provided to Replace.");
            return original;
          }
        }

        // Not even an S-expression.
        _ => {
          log(Channel::Error, 1, "Invalid input provided to Replace.");
          return original;
        }

      }; // end match on rule_expression

  // Apply each rule one by one until one of them changes the expression.
  let expression_hash = expression.hashed();
  for rule in rules {
    let new_expression = replace_all(expression.clone(), &rule, context);
    if expression_hash == new_expression.hashed() {
      // We have a winner!
      return new_expression;
    }
  }

  // No rules matched.
  expression.clone()
}


/// The internal version of NodeCount
pub fn node_count(expression: &Atom) -> usize {

  match expression {
    Atom::SExpression(children) => {
      let mut accumulator = 0usize;
      for child in children.iter() {
        accumulator += node_count(child);
      }
      accumulator
    }

    _ => 1usize
  }

}

/// A metric of expression complexity, counts the leaves and internal nodes of the expression.
/// Implements calls matching
///     `NodeCount[exp_] := built-in[exp]`
pub fn NodeCount(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "NodeCount called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  let expression = &arguments[&SExpression::variable_static_str("exp")];

  Atom::Integer(BigInteger::from(node_count(expression)))
}


/// Implements calls matching
///     `Part[exp_, n_] := built-in[exp, n]`
pub fn Part(arguments: SolutionSet, original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Part called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  // let mut arg_iter = arguments.values();
  let n          = &arguments[&SExpression::variable_static_str("n")];   //arg_iter.next().unwrap();
  let expression = &arguments[&SExpression::variable_static_str("exp")];

  if let Atom::Integer(m) = n {
    if ((m.to_i32_wrapping()) < 0) || (m.to_usize_wrapping() > expression.len()) {
      log(
        Channel::Error,
        1,
        format!(
          "Argument {} is out of bounds for expression of length {}",
          m,
          expression.len()
        ).as_str(),
      );
      return original;
    }

    if expression.kind() != AtomKind::SExpression {
      return expression.clone();
    }

    SExpression::part(&expression, m.to_usize_wrapping())
  } else {
    // Unevaluatable
    original
  }

}

/// Implements calls matching
///     `Head[exp_] := built-in[exp]`
pub fn Head(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Head called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  let arg: &Atom = arguments.values().next().unwrap();
  arg.head()
}


pub(crate) fn register_builtins(context: &mut Context) {

  register_builtin!(Head, "Head[exp_]", Attribute::Protected.into(), context);
  register_builtin!(Part, "Part[exp_, n_]", Attribute::Protected.into(), context);
  register_builtin!(NodeCount, "NodeCount[exp_]", Attribute::Protected.into(), context);
  register_builtin!(Replace, "Replace[exp_, rules_]", Attribute::Protected.into(), context);
  register_builtin!(ReplaceAll, "ReplaceAll[exp_, rules_]", Attribute::Protected.into(), context);
  register_builtin!(Occurs, "Occurs[needle_, haystack_]", Attribute::Protected.into(), context);

}
