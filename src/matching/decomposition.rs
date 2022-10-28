/*!

The code for Dec-F and Dec-A are nearly identical. Likewise for the code for Dec-C and Dec-AC. It
is factored out here. A few marker types distinguish the cases.

*/


use smallvec::smallvec;

use crate::{
  matching::{
    match_generator::{
      MatchGenerator,
      MaybeNextMatchResult,
      NextMatchResult,
      NextMatchResultList
    },
    MatchEquation
  },
  atom::SExpression,
};
#[allow(unused_imports)]
use crate::logging::{Channel, log};

/// Marker types for the different decomposition types.
pub trait DecompositionType {}

pub struct Associative;

impl DecompositionType for Associative {}

pub struct NonAssociative;

impl DecompositionType for NonAssociative {}

/// Decomposition under free/associative head.
/// ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)}, where ƒ is free and s∉Ꮙₛₑ.
pub struct RuleDecNonCommutative<T> where T: DecompositionType {
  me: MatchEquation,
  exhausted     : bool,
  phantom       : std::marker::PhantomData<T>
}

impl<T> RuleDecNonCommutative<T> where T: DecompositionType {
  pub fn new(match_equation: MatchEquation) -> RuleDecNonCommutative<T> {
    RuleDecNonCommutative {
      me: match_equation,
      exhausted: false,
      phantom  : std::marker::PhantomData::<T>::default()
    }
  }
}

// Dec-F: Decomposition under free head.
impl RuleDecNonCommutative<NonAssociative> {
  pub fn try_rule(me: &MatchEquation) -> Option<Self> {
    // Pattern: f[x,…], x not sequence variable
    // Ground:  g[a,…]
    // Identical to criteria for other Dec-type functions. The first of pattern_function cannot be a
    // sequence variable. It must be a non-sequence "term".

    if me.pattern.len() > 0
        && me.ground.len() > 0
        && SExpression::part(&me.pattern, 1).is_sequence_variable().is_none()
    {
      Some(
        RuleDecNonCommutative::<NonAssociative>::new(me.clone())
      )
    } else {
      None
    }
  }
}


// Dec-A: Decomposition under associative head.
impl RuleDecNonCommutative<Associative> {
  pub fn try_rule(me: &MatchEquation) -> Option<Self> {
    // The first of pattern_function cannot be a sequence variable. It must
    // be a function or a symbol, i.e. a non-sequence "term".

    if me.pattern.len() > 0
        && me.ground.len() > 0
        && SExpression::part(&me.pattern, 1).is_sequence_variable().is_none()
    {
      Some(
        RuleDecNonCommutative::new(me.clone())
      )
    } else {
      None
    }
  }
}


impl<T> MatchGenerator for RuleDecNonCommutative<T> where T: DecompositionType {
  fn match_equation(&self) -> MatchEquation {
    self.me.clone()
  }
}

impl<T> Iterator for RuleDecNonCommutative<T> where T: DecompositionType {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    if self.exhausted {
      None
    } else {
      self.exhausted = true;


      let result_variable_equation =
          NextMatchResult::eq(
            self.me.pattern_first(),
            SExpression::part(&self.me.ground, 1)
          );

      let match_equation_ground = SExpression::duplicate_with_rest(&self.me.ground);
      let result_function_equation =
          NextMatchResult::eq(
            self.me.pattern_rest(),
            match_equation_ground
          );

      Some(smallvec![
        result_variable_equation,
        result_function_equation
      ])
    } // end else not exhausted
  }
}


pub struct RuleDecCommutative<T> where T: DecompositionType {
  match_equation: MatchEquation,
  /// Which child of the ground function we are matching on.
  term_idx: u32,
  phantom: std::marker::PhantomData<T>
}

impl<T> MatchGenerator for RuleDecCommutative<T> where T: DecompositionType {
  fn match_equation(&self) -> MatchEquation {
    self.match_equation.clone()
  }
}

impl<T> Iterator for RuleDecCommutative<T> where T: DecompositionType {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {

    // Is there another term?
    if self.term_idx as usize == self.match_equation.ground.len() {

      return None;
    }

    // Construct the result.
    let term_equation = NextMatchResult::eq(
      self.match_equation.pattern_first(),
      SExpression::part(&self.match_equation.ground, self.term_idx as usize + 1)
    );

    let new_ground_function = { // scope of children
      let children
          = SExpression::children(
            &self.match_equation.ground
          )[1..].iter()
                .enumerate()
                .filter_map(|(k, v)| if k != self.term_idx as usize { Some(v.clone()) } else { None })
                .collect::<Vec<_>>();
      SExpression::new(self.match_equation.ground.head(), children)
    };

    let function_equation = NextMatchResult::eq(
      self.match_equation.pattern_rest(),
      new_ground_function
    );

    // We just iterate over the children of the ground.
    self.term_idx += 1;

    Some(smallvec![term_equation, function_equation])
  }
}

impl<T> RuleDecCommutative<T> where T: DecompositionType {
  pub fn new(me: MatchEquation) -> RuleDecCommutative<T> {
    RuleDecCommutative {
      match_equation: me,
      term_idx: 0,
      phantom : std::marker::PhantomData::<T>::default()
    }
  }
}

// Dec-C: Decomposition under commutative head.
impl RuleDecCommutative<NonAssociative> {
  pub fn try_rule(me: &MatchEquation) -> Option<RuleDecCommutative<NonAssociative>> {
    // The first of pattern_function cannot be a sequence variable. It must be a function or a
    // symbol, i.e. a non-sequence "term".

    if me.pattern.len() > 0
        && me.ground.len() > 0
        && SExpression::part(&me.pattern, 1).is_sequence_variable().is_none()
    {
      Some(
        RuleDecCommutative::new(me.clone())
      )
    } else {
      None
    }

  }
}


// Dec-AC: Decomposition under associative-commutative head.
impl RuleDecCommutative<Associative> {
  pub fn try_rule(me: &MatchEquation) -> Option<RuleDecCommutative<Associative>> {
    // The first of pattern_function cannot be a sequence variable. It must
    // be a function or a symbol, i.e. a non-sequence "term".

    if me.pattern.len() > 0
        && me.ground.len() > 0
        && SExpression::part(&me.pattern, 1).is_sequence_variable().is_none()
    {
      Some(
        RuleDecCommutative::new(me.clone())
      )
    } else {
      None
    }

  }
}


// tests
// The tests are on the composing generators.
