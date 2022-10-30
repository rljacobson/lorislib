/*!

Expression manipulation

 */
#![allow(non_snake_case)]
use std::{
  rc::Rc
};
use std::collections::{HashMap, HashSet};



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
    AtomKind
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
use crate::evaluate::replace_all_bound_variables;
use crate::interner::InternedString;
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

/// Utility function to replace the pattern variables in the rule with fresh variables. This step is necessary any
/// time there is the possibility that the variable names in a pattern could collide with the symbols in the subject.
pub fn give_fresh_variables(substitutions: &SolutionSet, context: &mut Context) -> SolutionSet {
  // The names of the fresh variables are not valid identifiers so that user code cannot conflict with them. Also,
  // the names don't repeat until ~18.4 millions of trillions of names have been generated, sometime after the heat
  // death of the universe. We give the global context the job of keeping track of fresh variables.
  let mut new_substitutions = SolutionSet::new();
  let mut fresh_variables = HashMap::new();

  for (lhs, rhs) in substitutions{
    // Pattern variables on the rhs are treated just like any other expression.
    if let Some(variables) = get_all_variable_names(&lhs){
      fresh_variables.clear(); // We'll reuse this.
      for variable_name in variables{
        let old_symbol = Atom::Symbol(variable_name);
        let new_symbol = context.fresh_variable();
        fresh_variables.insert(old_symbol, new_symbol);
      }

      new_substitutions.insert(
        replace_all_ground_terms(lhs.clone(), &fresh_variables),
        replace_all_ground_terms(rhs.clone(), &fresh_variables),
      );
    } else {
      new_substitutions.insert(lhs.clone(), rhs.clone());
    }
  }

  new_substitutions
}

/// Creates a set of names of all (pattern) variables appearing in `expression`.
pub fn get_all_variable_names(expression: &Atom) -> Option<HashSet<InternedString>> {
  let mut variables: HashSet<InternedString> = HashSet::new();

  // This is an obnoxious pattern.
  if let Some(name) = expression.is_variable() {
    variables.insert(name);
    return Some(variables);
  } else if let Some(name) = expression.is_sequence_variable() {
    variables.insert(name);
    return Some(variables);
  } else if let Some(name) = expression.is_null_sequence_variable() {
    variables.insert(name);
    return Some(variables);
  }

  if let Atom::SExpression(children) = expression {
    for names in children.iter().filter_map(|c| get_all_variable_names(c)) {
      variables.extend(names.iter());
    }
  }

  if variables.is_empty() {
    None
  } else {
    Some(variables)
  }

}

/// Internal version of `ReplaceAll`
/// Performs all substitutions in the given substitution set on expression.
/// It is the caller's responsibility to ensure that the substitutions have fresh variables.
/// Note: If you want to instantiate a set of _variable bindings_, which also have the type `SolutionSet`, use
/// `crate::evaluate::replace_all_bound_variables`, which replaces variables by name instead of using the pattern
/// matcher.
pub(crate) fn replace_all(expression: Atom, substitutions: &SolutionSet, context: &mut Context) -> Atom {
  // Is expression a key in substitutions?
  if let Some(replacement) = substitutions.get(&expression){
    // Great, we can skip the pattern matcher altogether.
    log(
      Channel::Debug,
      4,
      format!("Replacing {} with {}.", expression, replacement).as_str()
    );
    return replacement.clone();
  }

  // First, try to match expression itself.
  for (pattern, substitution) in substitutions {
    log(
      Channel::Debug,
      4,
      format!("Replacing all occurrences of pattern {} with {} in {}.", pattern, substitution, expression).as_str()
    );
    let mut matcher = Matcher::new(pattern.clone(), expression.clone(), context);
    match matcher.next(context) {

      Some(matched_substitution) => {
        // Match succeeded. Instantiate the variable bindings in the substitution.
        log(
          Channel::Debug,
          4,
          format!(
            "Pattern match gave substitutions {}, doing replacement in {}",
            display_solutions(&matched_substitution),
            &substitution
          ).as_str()
        );
        let result = replace_all_bound_variables(substitution, &matched_substitution, context);
        log(
          Channel::Debug,
          4,
          format!("...after replacement: {}.", result).as_str()
        );
        return result;
      }

      None => {
        // This pattern did not match. Try the next one.
        continue;
      }
    }

  } // end loop over patterns

  // Nothing matches `expression` itself. Now do the ReplaceAll on any children there may be, including the head.
  if let Atom::SExpression(children) = expression {
    let new_children = children.iter()
                               .map(|c| replace_all(c.clone(), substitutions, context))
                               .collect();

    Atom::SExpression(Rc::new(new_children))
  } else {
    // Cannot recurse, so ReplaceAll left this expression unchanged.
    expression.clone()
  }

}

/// A version of replace_all that assumes all substitutions are substitutions of ground terms and therefore do not
/// require the pattern matcher. Useful for replacing subexpressions of pattern variables, for example.
pub(crate) fn replace_all_ground_terms(expression: Atom, substitutions: &SolutionSet) -> Atom {
  // Is expression a key in substitutions?
  if let Some(replacement) = substitutions.get(&expression){
    // Great, we can skip the pattern matcher altogether.
    return replacement.clone();
  }

  // The `expression` is not a key. Do the replace on any children there may be, including the head.
  if let Atom::SExpression(children) = expression {
    let new_children = children.iter()
                               .map(|c| replace_all_ground_terms(c.clone(), substitutions))
                               .collect();

    Atom::SExpression(Rc::new(new_children))
  } else {
    // Cannot recurse, so ReplaceAll left this expression unchanged.
    expression
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

  let fresh_rules = give_fresh_variables(&rules, context);

  // Apply all rules at once.
  replace_all(expression.clone(), &fresh_rules, context)
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

  let expression       = &arguments[&SExpression::variable_static_str("exp")];
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
              log(Channel::Error, 1, "Invalid input provided to Replace. Nothing is a rule.");
              return original;
            }

            // Internally, a rule is a hashmap entry.
            rule_list.into_iter().map(|r| HashMap::from([r])).collect::<Vec<_>>()
          }

          // Single Rule
          else if let Some((lhs, rhs)) = rules_expression.is_rule() {
            vec![HashMap::from([(lhs, rhs)])]
          }

          // Invalid input.
          else {
            log(Channel::Error, 1, "Invalid input provided to Replace. Second argument is not an s-expr.");
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
    let fresh_rule = give_fresh_variables(&rule, context);
    let new_expression = replace_all(expression.clone(), &fresh_rule, context);

    if expression_hash != new_expression.hashed() {
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


#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn replace_ground_terms_test() {
    let expression   = parse("f[a, c_, b__, g___]^b").unwrap();
    let expected     = parse("f[a, c_, x__, g___]^x").unwrap();
    let substitution = HashMap::from([(Atom::Symbol(interned_static("b")), Atom::Symbol(interned_static("x")))]);


    let result = replace_all_ground_terms(expression.clone(), &substitution);
    println!("Before  : {}\nAfter   : {}\nExpected: {}", expression, result, expected);
    assert_eq!(result, expected);
  }


  #[test]
  fn replace_test() {
    let mut context = Context::without_built_ins(interned_static("Global"));
    let original    = parse("Replace[f[a, c_, b__, g___]^b, b->x]").unwrap(); // For illustration, not used.
    let expression  = parse("f[a, c_, b__, g___]^b").unwrap();
    let rule        = parse("b->x").unwrap();
    let expected    = parse("f[a, c_, x__, g___]^x").unwrap();
    let arguments   = HashMap::from([
      (SExpression::variable_static_str("exp"), expression.clone()),
      (SExpression::variable_static_str("rules"), rule)
    ]);
    set_verbosity(4);

    let result = Replace(arguments, original, &mut context);
    println!("Before  : {}\nAfter   : {}\nExpected: {}", expression, result, expected);
    assert_eq!(result, expected);
  }


  #[test]
  fn replace_all_test() {
    let mut context = Context::without_built_ins(interned_static("Global"));
    let original    = parse("f[a, c_, b__, g___]^b /. {b->x, a->c/d}").unwrap(); // For illustration, not used.
    let expression  = parse("f[a, c_, b__, g___]^b").unwrap();
    let rules = parse("{b->x, a->c/d}").unwrap();
    let expected    = parse("Power[f[Divide[c, d], c_, x__, g___], x]").unwrap();
    let arguments   = HashMap::from([
      (SExpression::variable_static_str("exp"), expression.clone()),
      (SExpression::variable_static_str("rules"), rules)
    ]);
    set_verbosity(4);

    let result = ReplaceAll(arguments, original, &mut context);
    println!("Before  : {}\nAfter   : {}\nExpected: {}", expression, result, expected);
    assert_eq!(result, expected);
  }

  #[test]
  fn give_fresh_variables_test() {
    let mut context  = Context::without_built_ins(interned_static("Global"));
    let lhs          = parse("q_*x^p_").unwrap();
    let rhs          = parse("q*f[p]").unwrap();
    let expected     = "[ Times❨‹tmp$0›, Power❨x, ‹tmp$1›❩❩ = Times❨tmp$0, f❨tmp$1❩❩ ]";
    let substitution = HashMap::from([
      (lhs, rhs)
    ]);
    set_verbosity(4);

    let result = give_fresh_variables(&substitution, &mut context);
    println!(
      "Before  : {}\nAfter   : {}\nExpected: {}",
       display_solutions(&substitution),
       display_solutions(&result),
       expected
    );
    // assert_eq!(result, expected);
  }

  #[test]
  fn complicated_replace_all_test() {
    let mut context = Context::without_built_ins(interned_static("Global"));
    let original    = parse("1 + 3*x^2 + 5*x^4 /. c_*x^p_ :> c*f[p]").unwrap(); // For illustration, not used.
    let expression  = parse("1 + 3*x^2 + 5*x^4").unwrap();
    let rules = parse("c_*x^p_ :> c*f[p]").unwrap();
    let expected    = parse("1 + 3*f[2] + 5*f[4]").unwrap();
    let arguments   = HashMap::from([
      (SExpression::variable_static_str("exp"), expression.clone()),
      (SExpression::variable_static_str("rules"), rules)
    ]);
    set_verbosity(4);

    let result = ReplaceAll(arguments, original, &mut context);
    println!("Before  : {}\nAfter   : {}\nExpected: {}", expression, result, expected);
    assert_eq!(result, expected);
  }
}
