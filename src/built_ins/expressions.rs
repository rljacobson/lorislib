/*!

Expression manipulation

 */
#![allow(non_snake_case)]
use std::{
  rc::Rc
};
use std::collections::HashMap;



use rug::{Integer as BigInteger};

 // For num_integer::binomial

use crate::{
  matching::{
    display_solutions,
    SolutionSet,
    Matcher
  },
  parse,
  atom::{
    Symbol,
    SExpression,
    Atom,
    AtomKind,
    SExpression::make_variable
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
};
use crate::built_ins::{occurs_check, register_builtin};
#[allow(unused_imports)]#[allow(unused_imports)]
use crate::interner::resolve_str;
#[allow(unused_imports)]
use crate::logging::set_verbosity;




/// Implements calls matching
///     `OccursQ[haystack_, needle_] := built-in[haystack, needle]`
pub(crate) fn OccursQ(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "OccursQ called with arguments {}",
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
pub(crate) fn replace_all(expression: Atom, substitutions: &SolutionSet, context: &mut Context) -> Atom {
  // The first time this function is called, the substitutions might be a set of `Rule`s with nontrivial patterns on
  // their lhs, patterns that may have several variables to bind--or no variables at all. Therefore, we cannot assume
  // that `substitutions` is just a set of variables and the values they are bound to.
  //
  // However, once a complicated pattern has matched, the result _is_ just a (possibly empty) set of variables and
  // their values.

  // Is expression a key in substitutions?
  if let Some(replacement) = substitutions.get(&expression){
    return replacement.clone();
  }


  match &expression {
    Atom::SExpression(children) => {
      // If expression is an s-expression, two (remaining) possibilities:
      //   1. There is a non-simple pattern that matches expression, creating a set of variable bindings.
      //   2. or there isn't a top-level match and the process needs to recurse into the children.

      for (pattern, substitution) in substitutions {
        if pattern.is_any_variable_kind() {
          // A variable will *match*, but it won't be the right replacement.
          continue;
        }

        log(
          Channel::Debug,
          4,
          format!("Replacing all occurrences of pattern {} with {} in {}.", pattern, substitution, expression).as_str()
        );
        let mut matcher = Matcher::new(pattern.clone(), expression.clone(), context);
        match matcher.next() {
          Some(matched_substitution) => {

            // On the other hand, matched_substitution might be a binding of several variables, or maybe a single
            // variable that is a child  or  a grandchild of `expression`. In this case, we must continue replacing
            // the bound variables in `substitution`
            log(
              Channel::Debug,
              4,
              format!(
                "Pattern match gave substitutions {}, doing replacement in {}",
                display_solutions(&matched_substitution),
                &substitution
              ).as_str()
            );
            // The pattern bound some variables.
            let result = replace_all(substitution.clone(), &matched_substitution, context);
            log(
              Channel::Debug,
              4,
              format!("...after replacement: {}.", result).as_str()
            );
            return result;
          }
          None => {
            continue;
          }
        }

      } // end loop over patterns

      // Recurse into children.
      let new_children = children.iter().map(|c| replace_all(c.clone(), substitutions, context)).collect();

      Atom::SExpression(Rc::new(new_children))
    }

    Atom::Symbol(name) => {
      // If expression is a symbol, it could be the name of a variable binding. This is a little annoying to check in
      // constant time. Because the keys are pattern variables, not symbols, we need to make variable version of
      // expresssion.

      // Look for a variable with the same name is a key in `substitutions`.
      let var = make_variable(expression.clone(), "Blank");
      if let Some(replacement) = substitutions.get(&var) {
        return replacement.clone();
      }
      let seq_var = make_variable(expression.clone(), "BlankSequence");
      if let Some(replacement) = substitutions.get(&seq_var) {
        return replacement.clone();
      }
      let null_seq_var = make_variable(expression.clone(), "BlankNullSequence");
      if let Some(replacement) = substitutions.get(&null_seq_var) {
        return replacement.clone();
      }
      expression
    }

    other => {
      // Remaining cases are literals. We already checked that we are not a key at the top of this function.
      expression
    }

  }
}


/// ReplaceAll[exp_, rules_]
/// Given a list of rules, performs all substitutions defined by the rules at once.
pub(crate) fn ReplaceAll(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
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
              log(
                Channel::Error,
                1,
                format!(
                  "Invalid input provided to Replace: rule_list.len={}, children.len={}",
                  rule_list.len(),
                  children.len()-1
                ).as_str()
              );
              return original;
            }

            // Internally, a set of rules is a hashmap.
            HashMap::from_iter(rule_list.into_iter())
          }

          // Single Rule
          else if let Some((lhs, rhs)) = rules_expression.is_rule() {
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
pub(crate) fn Replace(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
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
pub(crate) fn node_count(expression: &Atom) -> usize {

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
pub(crate) fn NodeCount(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
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
pub(crate) fn Part(arguments: SolutionSet, original: Atom, _: &mut Context) -> Atom {
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
pub(crate) fn Head(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
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

/// Implements calls matching
///     `exp[exp___] if exp is a sequence with Sequence occurring.
pub(crate) fn Sequence(arguments: SolutionSet, original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Sequence called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  // If exp has attribute SequenceHold, then do nothing.

  if let Atom::SExpression(mut children) = original {
    let mut new_children: Vec<Atom> = Vec::new();

    for mut child in Rc::make_mut(&mut children).drain(..) {
      match child {

        Atom::SExpression(ref mut grand_children) => {
          if grand_children[0] == Symbol::from_static_str("Sequence"){
            new_children.extend(Rc::make_mut(&mut *grand_children).drain(1.. ));
          } else {
            new_children.push(child);
          }
        }

        _ => {
          new_children.push(child);
        }
      }
    }

    Atom::SExpression(Rc::new(new_children))
  } else {
    original
  }
}


pub(crate) fn register_builtins(context: &mut Context) {

  register_builtin!(Head      , "Head[exp_]"                               , Attribute::Protected.into(), context);
  register_builtin!(Part      , "Part[exp_, n_]"                           , Attribute::Protected.into(), context);
  register_builtin!(NodeCount , "NodeCount[exp_]"                          , Attribute::Protected.into(), context);
  register_builtin!(Replace   , "Replace[exp_, rules_]"                    , Attribute::Protected.into(), context);
  register_builtin!(ReplaceAll, "ReplaceAll[exp_, rules_]"                 , Attribute::Protected.into(), context);
  register_builtin!(OccursQ   , "OccursQ[haystack_, needle_]"              , Attribute::Protected.into(), context);
  // Sequence is a bit of an oddball in that we don't care how the variables bind, and it is really only useful as an
  // up-value.
  {
    let symbol = interned_static("Sequence");
    let value  = SymbolValue::BuiltIn {
      pattern  : parse("exp___").unwrap(),
      condition: None,
      built_in : Sequence,
    };
    context.set_up_value(symbol, value);
    context.set_attribute(symbol, Attribute::Protected)
  };
}
