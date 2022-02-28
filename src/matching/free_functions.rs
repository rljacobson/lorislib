/*!
Rules for free symbols.
These rules apply when ƒ is free.

Dec-F: Decomposition under free head ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)}, where ƒ is free and s∉Ꮙₛₑ.

SVE-F: Sequence variable elimination under free head ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is free and S={x̅≈t̃₁}. An SVE-F match generator must enumerate all possible ways of choosing t̃₁.

*/

use std::{
  rc::Rc,
  default::Default
};

use smallvec::{
  smallvec,
  SmallVec
};

use crate::{
  atoms::Sequence,
  expression::ExpressionKind
};

use super::{
  destructure::DestructuredFunctionEquation,
  MatchEquation,
  match_generator::{
    MatchGenerator,
    MaybeNextMatchResult,
    NextMatchResult,
    NextMatchResultList
  },
  Substitution
};

/// Decomposition under free head.
/// ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)}, where ƒ is free and s∉Ꮙₛₑ.
pub struct RuleDecF {
  match_equation: MatchEquation,
  exhausted     : bool,
}

impl RuleDecF {
  pub fn new(match_equation: MatchEquation) -> RuleDecF {
    RuleDecF {
      match_equation,
      exhausted: false
    }
  }

  pub fn try_rule(dfe: &DestructuredFunctionEquation) -> Option<Self> {
    if (dfe.pattern_function.head() == dfe.ground_function.head())
        && (dfe.pattern_function.first().kind() == ExpressionKind::Variable)
        && (dfe.ground_function.len() > 1)
    {
      Some(
        RuleDecF {
          match_equation: dfe.match_equation.clone(),
          exhausted: false
        }
      )
    } else {
      None
    }
  }

}

impl MatchGenerator for RuleDecF {
    fn match_equation(&self) -> MatchEquation {
        self.match_equation.clone()
    }
}

impl Iterator for RuleDecF {
  type Item = NextMatchResultList;

    fn next(&mut self) -> MaybeNextMatchResult {
        if self.exhausted {
          None
        } else {
          self.exhausted = true;

          let dfe = DestructuredFunctionEquation::new(self.match_equation.clone());

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


          return Some(smallvec![
            result_variable_equation,
            result_function_equation
          ]);
        } // end else not exhausted
    }
}


// ƒ(x̅,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is free and S={x̅≈t̃₁}
pub struct RuleSVEF<'a> {
  dfe: DestructuredFunctionEquation<'a>,

  /// Have we produced the empty sequence as the first result yet?
  empty_produced: bool,
  /// A `Sequence`, holds the terms of the ground that we have attempted to match
  /// against so far.
  ground_sequence: Sequence,

}

impl<'a> MatchGenerator for RuleSVEF<'a> {
  fn match_equation(&self) -> MatchEquation {
    self.dfe.match_equation.clone()
  }
}

impl<'a> Iterator for RuleSVEF<'a> {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    // If we haven't produced the empty sequence, do that.
    if !self.empty_produced {
      self.empty_produced = true;
      return Some(self.make_next());
    }

    // Are there any more terms to take?
    if self.dfe.ground_function.len() == self.ground_sequence.len() {
      // No more terms.
      return None;
    }

    // Take the next term from the ground function.
    self.ground_sequence.children.push(
      self.dfe.ground_function.children[
        self.ground_sequence.len()
      ].clone()
    );

    // Construct the result.
    return Some(self.make_next());
  }
}

impl<'a> RuleSVEF<'a> {
  pub fn new(me: MatchEquation) -> RuleSVEF<'a> {
    RuleSVEF{
      dfe            : DestructuredFunctionEquation::new(me),
      ground_sequence: Sequence::default(),
      empty_produced : false
    }
  } // end new RuleSVEF

  // Constructs the next result using components of `self`.
  fn make_next(&self) -> SmallVec<[NextMatchResult; 3]> {
    let mut match_equation_ground = self.dfe.ground_function.duplicate_head();
    // Todo: Does this do the right thing when `ground_function.len()==ground_sequence.len()`?
    self.dfe.ground_function
        .children[self.ground_sequence.len()..]
        .clone_into(
          &mut match_equation_ground.children
        );

    let result_equation =
      NextMatchResult::MatchEquation(
        MatchEquation{
          pattern: self.dfe.pattern_rest.clone(),
          ground: Rc::new(match_equation_ground.into())
        }
      );

    let result_substitution = NextMatchResult::Substitution(
      Substitution{
        variable: self.dfe.pattern_first.clone(),
        ground: Rc::new(self.ground_sequence.clone().into()),
      }
    );

    return smallvec![result_equation, result_substitution];
  }


  pub fn try_rule(dfe: &DestructuredFunctionEquation) -> Option<Self> {

  }

}



#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    atoms::{
      SequenceVariable,
      Symbol,
      Function, Variable
    },
    expression::RcExpression
  };


  #[test]
  fn generate_rule_svef() {
    let x: RcExpression = Rc::new(SequenceVariable::from("x").into());
    let mut rest = ["u", "v", "w"].iter().map(|&n| Rc::new(Symbol::from(n).into())).collect::<Vec<RcExpression>>();
    let mut f = Function::with_symbolic_head("ƒ");

    f.push(x);
    f.children.extend(rest.drain(..));

    let mut g = Function::with_symbolic_head("ƒ");
    g.children = ["a", "b", "c"].iter().map(|&n| Rc::new(Symbol::from(n).into())).collect::<Vec<RcExpression>>();

    let me = MatchEquation{
        pattern: Rc::new(f.into()),
        ground: Rc::new(g.into()),
    };

    // println!("{}", me);

    let rule_svea = RuleSVEF::new(me);

    // for result in rule_svea {
    //   for e in result{
    //     println!("{}", e);
    //   }
    // }
    let result = rule_svea.flatten().map(|r| r.to_string()).collect::<Vec<String>>();
    let expected = [
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b, c❩",
      "«x»→()",
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c❩",
      "«x»→(a)",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(a, b)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(a, b, c)",
    ];

    assert_eq!(expected, result.as_slice());

  }

  #[test]
  fn generate_rule_decf() {
    let s: RcExpression = Rc::new(Variable::from("s").into());
    let mut rest = ["u", "v", "w"].iter().map(|&n| Rc::new(Symbol::from(n).into())).collect::<Vec<RcExpression>>();
    let mut f = Function::with_symbolic_head("ƒ");

    f.push(s);
    f.children.extend(rest.drain(..));

    let mut g = Function::with_symbolic_head("ƒ");
    g.children = ["a", "b", "c", "d"].iter().map(|&n| Rc::new(Symbol::from(n).into())).collect::<Vec<RcExpression>>();

    let me = MatchEquation{
        pattern: Rc::new(f.into()),
        ground: Rc::new(g.into()),
    };
    let rule_decf = RuleDecF::new(me);

    let expected = [
      "‹s› ≪ a",
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c, d❩"
    ];
    let result = rule_decf.flatten().map(|r| r.to_string()).collect::<Vec<String>>();

    assert_eq!(expected, result.as_slice());

  }

}
