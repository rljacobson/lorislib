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
pub struct DestructuredFunctionEquation<'a> {
  /// The original match equation as given.
  pub match_equation: MatchEquation,
  /// The original pattern function.
  pub pattern_function: Cow<'a, Function>,
  /// The immutable first term in the pattern.
  pub pattern_first: RcExpression,
  /// The immutable ƒ(s̃) that is always the LHS of the resulting match equation.
  pub pattern_rest: RcExpression,
  /// Literally the destructured ground function.
  pub ground_function: Cow<'a, Function>,
}

impl<'a> DestructuredFunctionEquation<'a>{
  pub fn new(me: MatchEquation) -> DestructuredFunctionEquation<'a> {
    // Destructure pattern
    if let Expression::Function(pattern_function) = me.pattern.as_ref() {

      let pattern_rest = Rc::new(pattern_function.duplicate_with_rest().into());
      let pattern_first = pattern_function.first().unwrap();

      // Destructure ground
      if let Expression::Function(ground_function) = me.ground.as_ref() {
        // let ground_function = f.clone();

        DestructuredFunctionEquation{
          match_equation: me,
          pattern_function: Cow::Borrowed(pattern_function),
          pattern_first,
          pattern_rest,
          ground_function: Cow::Borrowed(ground_function),
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
