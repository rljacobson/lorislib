/*!

A utility struct that destructures a match equation into its component parts.

Most rules have the form ƒ(a,b)≪ᴱƒ(c,d), and matchers for these rules need to
destructure this equation in the same way. This destructuring is factored out
into `DestructuredFunctionEquation` and its constructor.

*/

use crate::{
  atom::{
    Atom,
    SExpression
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
  pub pattern_first: Atom,
  /// The immutable ƒ(s̃) that is always the LHS of the resulting match equation.
  pub pattern_rest: Atom,
  /// Literally the destructured ground function.
  pub ground_function: Atom, // Must be `Atom::SExpression(..)`
}

impl DestructuredFunctionEquation{
  pub fn new(me: &MatchEquation) -> DestructuredFunctionEquation {

    // todo: Should `duplicate_with_rest` and `part` return `Result`? Right now they panic if given the wrong variant.
    //       But everything that calls it immediately `unwrap`s it anyway.
    let pattern_first = SExpression::part(me.pattern.clone(), 1);
    let pattern_rest = SExpression::duplicate_with_rest(me.pattern.clone());

    DestructuredFunctionEquation{
      match_equation: me.clone(),
      pattern_function: me.pattern.clone(),
      pattern_first,
      pattern_rest,
      ground_function: me.ground.clone(),
    }
  }
}
