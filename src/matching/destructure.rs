/*!

A utility struct that destructures a match equation into its component parts.

*/

use std::{borrow::Cow, rc::Rc};

use crate::{
  atoms::function::Function,
  expression::{RcExpression, Expression}
};
use super::{
  MatchEquation,

};

/**

Most rules have the form ƒ(a,b)≪ᴱƒ(c,d), and matchers for these rules need to
destructure this equation in the same way. This destructuring is factored out
into `DestructuredFunctionEquation` and its constructor.

*/
#[derive(Clone)]
pub struct DestructuredFunctionEquation {
  /// The original match equation as given.
  pub match_equation: MatchEquation,
  /// The original pattern function.
  pub pattern_function: Function,
  /// The immutable first term in the pattern.
  pub pattern_first: RcExpression,
  /// The immutable ƒ(s̃) that is always the LHS of the resulting match equation.
  pub pattern_rest: RcExpression,
  /// Literally the destructured ground function.
  pub ground_function: Function,
}

impl DestructuredFunctionEquation{
  pub fn new(mut me: MatchEquation) -> DestructuredFunctionEquation {
    // let mut  pattern = me.pattern.make_mut();
    // let mut ground = Rc::<Expression>::make_mut(&mut me.ground);

    // Destructure pattern
    if let Expression::Function(pattern_function) = me.pattern.as_ref() {

      let pattern_rest = Rc::new(pattern_function.duplicate_with_rest().into());
      let pattern_first = pattern_function.first().unwrap();

      // Destructure ground
      if let Expression::Function(ground_function) = me.ground.as_ref() {
        // let ground_function = f.clone();

        DestructuredFunctionEquation{
          match_equation: me.clone(),
          pattern_function: pattern_function.clone(),
          pattern_first,
          pattern_rest,
          ground_function: ground_function.clone(),
        }

      } // end destructure ground
      else {
        unreachable!();
      }
    } // end destructure pattern
    else {
      unreachable!();
    }
  }
}
