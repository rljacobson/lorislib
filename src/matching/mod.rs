mod destructure;
mod associative_commutative;
mod function_application;
mod associative;
mod commutative;
mod free_functions;
mod common;
mod matcher;
mod match_generator;
mod decomposition;

/*

# Data Generators and Structures

The central player in the algorithm is the `Matcher`, which roughly speaking
corresponds to a generator (in the software sense) of the substitutions generated
(in the mathematical sense) by a solved equation, Σ(eq). It is not precisely the
same, if I understand correctly, because a `Matcher` also generates substitutions
for every possible way that a rule can transform the same equation (instead of
choosing an alternative nondeterministicly). `Matchers` also generate the
corresponding matching equations, and `Matcher`s know how to "undo" whatever they
generated last (by popping things from stacks, described below).

We have the following stack structures:

  * The matching equation stack Γ
  * The substitution stack S
  * The `Matcher` stack

The equation (or `Matcher`) on the top of the equation stack (resp. `Matcher`
stack) is said to be the _active equation_ (resp. _active `Matcher`_).

# Algorithm

This algorithm is implemented in `matcher.rs` in the implementation of `Iterator`
for `Matcher`.

Start state: S = Ø, Γ = {pattern≪expression}.

0. Prepare the active matching equation. The equation at the top of the Γ stack
is active. If the LHS (the pattern) of the matching equation is a named variable,
query S to see if the variable has a substitution. If so, replace the variable
with its substitution and continue. (I need to check that the stack order
guarantees this substitution will be undone.) At most one transformation rule can
apply.

1. Act on the active equation.
1.a If no rule applies:
1.a.i   If the matcher stack is empty, halt with *FAILURE*.
1.a.ii. If there is an active match generator on top of the matcher stack,
          Undo the actions of the last match generated from this `Matcher`:
          1. pop the top equations in Γ pushed by the last match.
          2. pop the top  substitutions in S pushed by the last match.
        Proceed to Step 2.
1.b If a rule applies, create the `Matcher` for the rule, (provide it the
equation), and push it into the `Matcher` stack. It is now the active `Matcher`.

2. Request a new match.
2.a If there is no active `Matcher` on top of the `Matcher` stack, return with *FAILURE*.
2.b If there is an active `Matcher`, call `next()` on the active match generator. This
generates zero or more substitutions which are stored in S (pushed onto the S
stack) and zero or more matching equations which are stored in Γ.

3. Act on the result of `next()`.
3.a. If the match generator is exhausted (returns `None`), proceed to Step 4.
3.b. If Γ is empty, return with *SUCCESS*.
3.c. Otherwise, proceed to Step 0.

4. Same as 1.a.ii, but pop `Matcher` from the stack before proceeding to Step 2.

SUCCESS: To obtain additional matches, proceed from Step 3.b to Step 1.a.ii.

*/

use std::{collections::HashMap, fmt::Display};

pub use matcher::{Matcher};
use crate::{
  expression::RcExpression,
  atom::SExpression
};

/// A map from a variable / sequence variable to the ground term is it bound to.
pub type SolutionSet = HashMap<RcExpression, RcExpression>;


#[derive(Clone)]
pub struct MatchEquation {
  pub(crate) pattern: RcExpression,
  pub(crate) ground : RcExpression
}

impl Display for MatchEquation {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} ≪ {}", self.pattern, self.ground)
  }
}



/// A map from pattern expressions to the expressions they match.
#[derive(Clone)]
pub struct Substitution{
  /// Variable or sequence variable.
  variable: RcExpression,
  ground  : RcExpression
}


impl Display for Substitution {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}→{}", self.variable, self.ground)
  }
}



#[cfg(test)]
mod tests {
  use std::rc::Rc;
  
  use crate::{
    atom::{
      Atom,
      SExpression,
      Symbol,
    },
    attributes::Attribute,
    logging::set_verbosity,
    matching::matcher::display_solutions
  };
  
  use super::*;

  #[test]
  /// Solve ƒ()≪ᴱƒ(), ƒ is A or AC
  fn match_empty_functions(){
    let mut f = SExpression::with_str_head("ƒ");
    f.attributes.set(Attribute::Associative);
    let g = f.duplicate_head();

    let me = MatchEquation{
      pattern: Rc::new(f.into()),
      ground: Rc::new(g.into()),
    };

    let mut matcher = Matcher::new(me.pattern.clone(), me.ground);
    let result: Vec<String> = matcher.map(|s| display_solutions(&s)).collect();
    assert_eq!("EMPTY", result.join(", "));
  }

  // The following numbered tests are from p. 37 of Dundua, the numbers coming from the paper.

  #[test]
  /// Solve ƒ(x̅)≪ᴱƒ(a), ƒ is A or AC
  fn problem5() {
    // set_verbosity(5);
    let mut f = SExpression::with_str_head("ƒ");
    f.attributes.set(Attribute::Associative);
    let x = Rc::new(SExpression::sequence_variable("x").into());
    f.push(x);

    let mut g = f.duplicate_head();
    let a = Rc::new(Symbol::from_static_str("a").into());
    g.push(a);

    let me = MatchEquation{
      pattern: Rc::new(f.into()),
      ground: Rc::new(g.into()),
    };

    let mut matcher = Matcher::new(me.pattern.clone(), me.ground);
    let result: Vec<String> = matcher.map(|s| display_solutions(&s)).collect();

    assert_eq!("{«x» = a, «x» = ƒ[a]}", format!("{{{}}}", result.join(", ")));
  }

  #[test]
  /// Solve ƒ(x,y)≪ᴱƒ(a,b), ƒ is AC
  fn problem7() {
    // set_verbosity(5);

    let mut f = SExpression::with_str_head("ƒ");
    f.attributes.set(Attribute::Associative);
    f.attributes.set(Attribute::Commutative);
    let x = Rc::new(SExpression::variable("x").into());
    f.push(x);
    let y = Rc::new(SExpression::variable("y").into());
    f.push(y);

    let mut g = f.duplicate_head();
    let a = Rc::new(Symbol::from_static_str("a").into());
    g.push(a);
    let b = Rc::new(Symbol::from_static_str("b").into());
    g.push(b);

    let me = MatchEquation{
      pattern: Rc::new(f.into()),
      ground: Rc::new(g.into()),
    };

    // println!("{}", me);

    let mut matcher = Matcher::new(me.pattern.clone(), me.ground);

    // for result in &mut Matcher::new(me.pattern.clone(), me.ground) {
    //   println!("{}", display_solutions(&result));
    // }

    let expected = [
      #[cfg(not(feature = "strict-associativity"))]
          "‹x› = ƒ[], ‹y› = ƒ[a, b]", // Not allowed by strict-associativity.
      "‹x› = ƒ[a], ‹y› = ƒ[b]",
      "‹x› = ƒ[a], ‹y› = b",
      "‹x› = ƒ[b], ‹y› = ƒ[a]",
      "‹x› = ƒ[b], ‹y› = a",
      #[cfg(not(feature = "strict-associativity"))]
          "‹x› = ƒ[a, b], ‹y› = ƒ[]", // Not allowed by strict-associativity.
      "‹x› = a, ‹y› = ƒ[b]",
      "‹x› = a, ‹y› = b",
      "‹x› = b, ‹y› = ƒ[a]",
      "‹x› = b, ‹y› = a"
    ];

    let result: Vec<String> = matcher.map(|s| display_solutions(&s)).collect();
    assert_eq!(expected, result.as_slice());

    // println!("{{{}}}", result.join(", "));
  }


  /// Solve ƒ[‹x›] ≪ ƒ[].
  /// No solution for strict associativity. One solution for (regular) associativity.
  #[test]
  fn match_empty_associative_function() {
    // set_verbosity(5);

    let mut f = SExpression::with_str_head("ƒ");
    f.attributes.set(Attribute::Associative);
    f.attributes.set(Attribute::Commutative);
    let x = Rc::new(SExpression::variable("x").into());
    f.push(x);

    let g = f.duplicate_head();

    let me = MatchEquation{
      pattern: Rc::new(f.into()),
      ground: Rc::new(g.into()),
    };

    let mut matcher = Matcher::new(me.pattern.clone(), me.ground);

    let result: Vec<String> = matcher.map(|s| display_solutions(&s)).collect();

    #[cfg(not(feature = "strict-associativity"))]
    assert_eq!("‹x› = ƒ[]", result.join(", "));
    #[cfg(feature = "strict-associativity")]
    assert_eq!("", result.join(", ")); // Empty
  }
}
