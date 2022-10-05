/*!
The common rules apply in any theory.

T: Trivial s ≪ᴱs ⇝ᵩ ∅.

IVE: Individual variable elimination x≪ᴱt⇝ₛ∅ where S ={x≈t}.

FVE: Function variable elimination X(s̃)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃)≪ᴱƒ(t̃)}, where S={X≈ƒ}.

*/

use std::cell::Cell;
use std::rc::Rc;

use smallvec::smallvec;

use crate::{
  expression::{
    Expression,
    ExpressionKind
  },
  atoms::Function
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

    if match_equation.pattern.kind() == ExpressionKind::Variable
        && match_equation.ground.kind() != ExpressionKind::Sequence
        && match_equation.ground.kind() != ExpressionKind::SequenceVariable
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

      // This is a bit of a mess because of the destructuring, but all it does is
      // create a new expression from `pattern` but with the `ground`'s
      // head.

      match (
              self.match_equation.pattern.as_ref(),
              self.match_equation.ground.as_ref()
            )
      {

        (
          Expression::Function(
            Function{
              head: pattern_head,
              children: pattern_children,
              attributes: pattern_attributes,
              ..
            }
          ),
          Expression::Function(
            Function{
              head: ground_head,
              ..
            }
          ),
        ) => {
          let substitution =
            NextMatchResult::Substitution(
              Substitution{
                variable: pattern_head.clone(),
                ground  : ground_head.clone(),
              }
            );
          let new_match_equations = NextMatchResult::MatchEquation(
              MatchEquation {
                pattern: Rc::new(Expression::Function(
                  Function{
                    head: ground_head.clone(),
                    children: pattern_children.clone(),
                    attributes: *pattern_attributes,
                    cached_hash: Cell::new(0)
                  }
                )),
                ground: self.match_equation.ground.clone(),
              }
            );

          Some(
            smallvec![
              new_match_equations,
              substitution
            ]
          )
        }

        _ => {
          unreachable!()
        }

      } // end match

    } // end else not exhausted
  } // end next
}


impl RuleFVE {
  pub fn try_rule(match_equation: &MatchEquation) -> Option<Self> {

    if let Expression::Function( Function{ head, ..} )
            = match_equation.pattern.as_ref() {
      if head.kind() == ExpressionKind::Variable
          && match_equation.ground.kind() == ExpressionKind::Function {
        return
          Some(
            RuleFVE{
              match_equation: match_equation.clone(),
              exhausted     : false,
            }
          );

      } // end inner if
    } // end if let

    None

  }
}
