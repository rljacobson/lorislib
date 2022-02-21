/*!
The common rules apply in any theory.

T: Trivial s ≪ᴱs ⇝ᵩ ∅.

IVE: Individual variable elimination x≪ᴱt⇝ₛ∅ where S ={x≈t}.

FVE: Function variable elimination X(s̃)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃)≪ᴱƒ(t̃)}, where S={X≈ƒ}.

*/

use tinyvec::array_vec;

use super::{MatchEquation, matcher::Matcher, Substitution};

/// Trivial elimination
pub struct RuleT {
  match_equation: MatchEquation,
  exhausted     : bool,
}

impl Matcher for RuleT {
    fn match_equation(&self) -> MatchEquation {
        self.match_equation.clone()
    }

    fn next(&mut self) -> Option<(super::NewMatchEquations, Option<super::Substitution>)> {
        if self.exhausted {
          None
        } else {
          self.exhausted = true;
          Some(
            (
              array_vec![],
              None
            )
          )
        }
    }
}


/// Individual variable elimination
pub struct RuleIVE {
  match_equation: MatchEquation,
  exhausted     : bool,
}


impl Matcher for RuleIVE {
    fn match_equation(&self) -> MatchEquation {
        self.match_equation.clone()
    }

  fn next(&mut self) -> Option<
    (
      super::NewMatchEquations,
      Option<super::Substitution>
    )
  > {
    if self.exhausted {
      None
    } else {
      self.exhausted = true;
      Some(
        (
          array_vec![],
          Some(
            Substitution{
              variable: self.match_equation.pattern,
              ground  : self.match_equation.ground,
            }
          )
        )
      )
    }
  }
}



/// Function variable elimination
pub struct RuleFVE {
  match_equation: MatchEquation,
  exhausted     : bool,
}
