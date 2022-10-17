/*!

A utility struct that destructures a match equation into its component parts.

Most rules have the form ƒ(a,b)≪ᴱƒ(c,d), and matchers for these rules need to
destructure this equation in the same way. This destructuring is factored out
into `DestructuredFunctionEquation` and its constructor.

*/

use std::rc::Rc;

use crate::{
  atom::Atom,
  expression::{
    RcExpression,
    Expression
  }
};
use super::{
  MatchEquation,
};

/**



*/
#[derive(Clone)]
pub struct DestructuredFunctionEquation {
  /// The original match equation as given.
  pub match_equation: MatchEquation,
  /// The original pattern function.
  pub pattern_function: Atom, // Must be `Atom::SExpression(..)`
  /// The immutable first term in the pattern.
  pub pattern_first: RcExpression,
  /// The immutable ƒ(s̃) that is always the LHS of the resulting match equation.
  pub pattern_rest: RcExpression,
  /// Literally the destructured ground function.
  pub ground_function: Atom, // Must be `Atom::SExpression(..)`
}

impl DestructuredFunctionEquation{
  pub fn new(me: &MatchEquation) -> Result<DestructuredFunctionEquation,()> {
    // let mut  pattern = me.pattern.make_mut();
    // let mut ground = Rc::<Expression>::make_mut(&mut me.ground);

    // Destructure pattern
    if let Expression::Function(pattern_function) = me.pattern.as_ref() {

      let pattern_rest = Rc::new(pattern_function.duplicate_with_rest().into());
      let pattern_first = pattern_function.first().ok_or(())?;

      // Destructure ground
      if let Expression::Function(ground_function) = me.ground.as_ref() {
        // let ground_function = f.clone();

        let dfe =
        DestructuredFunctionEquation{
          match_equation: me.clone(),
          pattern_function: pattern_function.clone(),
          pattern_first,
          pattern_rest,
          ground_function: ground_function.clone(),
        };

        Ok(dfe)

      } // end destructure ground
      else {
        Err(())
      }
    } // end destructure pattern
    else {
      Err(())
    }
  }
}
