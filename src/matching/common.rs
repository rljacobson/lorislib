/*!
The common rules apply in any theory.

T: Trivial s ≪ᴱs ⇝ᵩ ∅.

IVE: Individual variable elimination x≪ᴱt⇝ₛ∅ where S ={x≈t}.

FVE: Function variable elimination X(s̃)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃)≪ᴱƒ(t̃)}, where S={X≈ƒ}.

*/


use smallvec::smallvec;

use crate::{
  atom::{
    AtomKind,
    SExpression,
  }
};

use super::{
  MatchEquation,
  match_generator::{
    MatchGenerator,
    NextMatchResult,
    MaybeNextMatchResult, NextMatchResultList
  },
  Substitution,
};

/// Trivial elimination: s ≪ᴱs
pub struct RuleT {
  match_equation: MatchEquation,
  exhausted     : bool,
}

impl MatchGenerator for RuleT {
  fn match_equation(&self) -> MatchEquation {
    self.match_equation.clone()
  }
}

impl Iterator for RuleT {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    if self.exhausted {
      None
    } else {
      self.exhausted = true;
      Some(smallvec![])
    }
  }
}

impl RuleT {

  pub fn new(match_equation: MatchEquation) -> RuleT {
    RuleT {
      match_equation,
      exhausted: false
    }
  }

  pub fn try_rule(match_equation: &MatchEquation) -> Option<Self> {
    if match_equation.pattern == match_equation.ground {
      Some(
        RuleT{
          match_equation: match_equation.clone(),
          exhausted     : false
        }
      )
    } else {
      None
    }
  }
}


/// Individual variable elimination
pub struct RuleIVE {
  match_equation: MatchEquation,
  exhausted     : bool,
}

impl MatchGenerator for RuleIVE {
    fn match_equation(&self) -> MatchEquation {
        self.match_equation.clone()
    }
}

impl Iterator for RuleIVE {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    if self.exhausted {
      None
    } else {

      self.exhausted = true;

      Some(
        smallvec![
          NextMatchResult::Substitution(
            Substitution{
              variable: self.match_equation.pattern.clone(),
              ground  : self.match_equation.ground.clone(),
            }
          )
        ]
      )

    }
  }
}


impl RuleIVE {
  pub fn try_rule(match_equation: &MatchEquation) -> Option<Self> {
    // Pattern:  x_
    // Ground: Not a sequence or sequence variable.
    if match_equation.pattern.is_variable().is_some()
        && match_equation.ground.is_sequence().is_none()
        && match_equation.ground.is_sequence_variable().is_none()
    {
      Some(
            RuleIVE {
              match_equation: match_equation.clone(),
              exhausted: false
            }
          )
    } else {
      None
    }

  }
}

/// Function variable elimination
pub struct RuleFVE {
  match_equation: MatchEquation,
  exhausted     : bool,
}


impl MatchGenerator for RuleFVE {
  fn match_equation(&self) -> MatchEquation {
      self.match_equation.clone()
  }
}

impl Iterator for RuleFVE {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    if self.exhausted {
      None
    } else {
      self.exhausted = true;

      // Create a new expression from `pattern` but with the `ground`'s  head.
      let substitution =
          NextMatchResult::Substitution(
            Substitution{
              variable: self.match_equation.pattern.head(), // Pattern head, the variable
              ground  : self.match_equation.ground.head(),  // Ground head
            }
          );
      let new_match_equations =
          NextMatchResult::MatchEquation(
            MatchEquation {
              pattern: // The pattern with it's head replaced by ground's head.
                SExpression::new_swapped_head(
                  self.match_equation.ground.head(),
                  SExpression::children(&self.match_equation.pattern).as_ref()
                ),
              ground: self.match_equation.ground.clone(),
            }
          );

      Some(smallvec![new_match_equations, substitution])
    } // end else not exhausted
  } // end next
}


impl RuleFVE {
  pub fn try_rule(match_equation: &MatchEquation) -> Option<Self> {
    // Pattern: <f>[…]
    // Ground :  g[…]
    if SExpression::is_head_variable(&match_equation.pattern).is_some()
        && match_equation.ground.kind() == AtomKind::SExpression {
      Some(
        RuleFVE{
          match_equation: match_equation.clone(),
          exhausted     : false,
        }
      )
    } else {
      None
    }
  }
}



// tests
// The tests are on the composing generators.
