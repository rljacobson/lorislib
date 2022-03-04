/*!

The code for Dec-F and Dec-A are nearly identical. Likewise for the code for Dec-C and Dec-AC. It
is factored out here.

*/

use std::rc::Rc;

use smallvec::smallvec;

use crate::matching::destructure::DestructuredFunctionEquation;
use crate::matching::match_generator::{MatchGenerator, MaybeNextMatchResult, NextMatchResult, NextMatchResultList};
use crate::matching::MatchEquation;
use crate::expression::ExpressionKind;


/// Marker types for the different decomposition types.
pub trait DecompositionType {}
pub struct Associative;
impl DecompositionType for Associative {}
pub struct NonAssociative;
impl DecompositionType for NonAssociative {}

/// Decomposition under free head.
/// ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)}, where ƒ is free and s∉Ꮙₛₑ.
pub struct RuleDecNonCommutative<T> where T: DecompositionType {
  match_equation: MatchEquation,
  exhausted     : bool,
  phantom       : std::marker::PhantomData<T>
}

impl<T> RuleDecNonCommutative<T> where T: DecompositionType {
  pub fn new(match_equation: MatchEquation) -> RuleDecNonCommutative<T> {
    RuleDecNonCommutative {
      match_equation,
      exhausted: false,
      phantom: std::marker::PhantomData::<T>::default()
    }
  }
}

// Dec-F: Decomposition under free head.
impl RuleDecNonCommutative<NonAssociative> {

  pub fn try_rule(dfe: &DestructuredFunctionEquation) -> Option<Self> {
    // Identical to criteria for other Dec-type functions. The first of pattern_function cannot be a
    // sequence variable. It must be a function or a symbol, i.e. a non-sequence "term".

    if dfe.pattern_function.len() > 0
        && dfe.ground_function.len() > 0
    {
      let first = dfe.pattern_function.part(0);

      // Cannot be function variable.
      // if let Expression::Function(function) = first.as_ref() {
      //   if function.is_function_variable() {
      //     return None;
      //   }
      // }

      // Cannot be a variable-kind: function variable, sequence variable, variable.
      let expr_kind = first.kind();
      if expr_kind != ExpressionKind::SequenceVariable
      // && expr_kind != ExpressionKind::Variable
      {
        return Some(
          RuleDecNonCommutative {
            match_equation: dfe.match_equation.clone(),
            exhausted: false,
            phantom: std::marker::PhantomData::<NonAssociative>::default()
          }
        )
      }
    }

    None
  }

}


// Dec-A: Decomposition under free head.
impl RuleDecNonCommutative<Associative> {

  pub fn try_rule(dfe: &DestructuredFunctionEquation) -> Option<Self> {
    // The first of pattern_function cannot be a sequence variable or individual variable. It must
    // be a function or a symbol, i.e. a non-sequence "term".

    if dfe.pattern_function.len() > 0
        && dfe.ground_function.len() > 0
    {
      let first = dfe.pattern_function.part(0);

      // Cannot be function variable.
      // if let Expression::Function(function) = first.as_ref() {
      //   if function.is_function_variable() {
      //     return None;
      //   }
      // }

      // Cannot be a variable-kind: function variable, sequence variable, variable.
      let expr_kind = first.kind();
      if expr_kind != ExpressionKind::SequenceVariable
          && expr_kind != ExpressionKind::Variable
      {
        return Some(
          RuleDecNonCommutative {
            match_equation: dfe.match_equation.clone(),
            exhausted: false,
            phantom: std::marker::PhantomData::default()
          }
        )
      }
    }

    None
  }

}



impl<T> MatchGenerator for RuleDecNonCommutative<T> where T: DecompositionType {
  fn match_equation(&self) -> MatchEquation {
    self.match_equation.clone()
  }
}

impl<T> Iterator for RuleDecNonCommutative<T> where T: DecompositionType {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    if self.exhausted {
      None
    } else {
      self.exhausted = true;

      let dfe = DestructuredFunctionEquation::new(&self.match_equation).unwrap();

      let result_variable_equation =
          NextMatchResult::eq(
            dfe.pattern_first,
            dfe.ground_function.first().unwrap()
          );

      let match_equation_ground = dfe.ground_function.duplicate_with_rest();
      let result_function_equation =
          NextMatchResult::eq(
            dfe.pattern_rest,
            Rc::new(match_equation_ground.into())
          );


      Some(smallvec![
            result_variable_equation,
            result_function_equation
          ])
    } // end else not exhausted
  }
}



pub struct RuleDecCommutative<T> where T: DecompositionType {
  dfe: DestructuredFunctionEquation,
  /// Which child of the ground function we are matching on.
  term_idx: u32,
  phantom: std::marker::PhantomData<T>
}

impl<T> MatchGenerator for RuleDecCommutative<T> where T: DecompositionType {
  fn match_equation(&self) -> MatchEquation {
    self.dfe.match_equation.clone()
  }
}

impl<T> Iterator for RuleDecCommutative<T> where T: DecompositionType {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {

    // Is there another term?
    if self.term_idx as usize == self.dfe.ground_function.len() {
      return None;
    }

    // Construct the result.
    let term_equation = NextMatchResult::eq(
      self.dfe.pattern_first.clone(),
      self.dfe.ground_function
          .children[self.term_idx as usize]
          .clone()
    );

    let mut new_ground_function = self.dfe.ground_function.duplicate_head();
    new_ground_function.children =
        self.dfe.ground_function
            .children
            .iter()
            .enumerate()
            .filter_map(|(k, v)| if k != self.term_idx as usize {Some(v.clone())} else {None})
            .collect::<Vec<_>>();

    let function_equation = NextMatchResult::eq(
      self.dfe.pattern_rest.clone(),
      Rc::new(new_ground_function.into())
    );

    // We just iterate over the children of the ground.
    self.term_idx += 1;

    Some(smallvec![term_equation, function_equation])
  }
}

impl<T> RuleDecCommutative<T> where T: DecompositionType {
  pub fn new(me: MatchEquation) -> RuleDecCommutative<T> {
    let dfe = DestructuredFunctionEquation::new(&me).unwrap();
    RuleDecCommutative {
      dfe,
      term_idx: 0,
      phantom: std::marker::PhantomData::<T>::default()
    }
  }
}

// Dec-C: Decomposition under commutative head.
impl RuleDecCommutative<NonAssociative> {
  pub fn try_rule(dfe: &DestructuredFunctionEquation) -> Option<RuleDecCommutative<NonAssociative>> {
    // The first of pattern_function cannot be a sequence variable. It must be a function or a
    // symbol, i.e. a non-sequence "term".

    if dfe.pattern_function.len() > 0
        && dfe.ground_function.len() > 0
    {
      let first = dfe.pattern_function.part(0);

      // Cannot be function variable.
      // if let Expression::Function(function) = first.as_ref() {
      //   if function.is_function_variable() {
      //     return None;
      //   }
      // }

      // Cannot be a variable-kind: function variable, sequence variable, variable.
      let expr_kind = first.kind();
      if expr_kind != ExpressionKind::SequenceVariable
      // && expr_kind != ExpressionKind::Variable
      {
        return Some(
          RuleDecCommutative {
            dfe: dfe.clone(),
            term_idx: 0,
            phantom: std::marker::PhantomData::default()
          }
        )
      }
    }

    None
  }

}


// Dec-AC: Decomposition under associative-commutative head.
impl RuleDecCommutative<Associative> {
  pub fn try_rule(dfe: &DestructuredFunctionEquation) -> Option<RuleDecCommutative<Associative>> {
    // The first of pattern_function cannot be a sequence variable or individual variable.. It must
    // be a function or a symbol, i.e. a non-sequence "term".

    if dfe.pattern_function.len() > 0
        && dfe.ground_function.len() > 0
    {
      let first = dfe.pattern_function.part(0);

      // Cannot be function variable.
      // if let Expression::Function(function) = first.as_ref() {
      //   if function.is_function_variable() {
      //     return None;
      //   }
      // }

      // Cannot be a variable-kind: function variable, sequence variable, variable.
      let expr_kind = first.kind();
      if expr_kind != ExpressionKind::SequenceVariable
          && expr_kind != ExpressionKind::Variable
      {
        return Some(
          RuleDecCommutative {
            dfe: dfe.clone(),
            term_idx: 0,
            phantom: std::marker::PhantomData::default()
          }
        )
      }
    }

    None
  }

}
