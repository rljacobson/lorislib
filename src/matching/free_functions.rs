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
  atom::Atom,
  expression::ExpressionKind,
  matching::decomposition::{
    NonAssociative,
    RuleDecNonCommutative
  }
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


pub type RuleDecF = RuleDecNonCommutative<NonAssociative>;

// ƒ(x̅,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is free and S={x̅≈t̃₁}
pub struct RuleSVEF {
  pub(crate) dfe: DestructuredFunctionEquation,

  /*
    In Dundua, the strict associativity axiom is
      ƒ(x̅, ƒ(y̅₁, y, y̅₂), z̅) = ƒ(x̅, y̅₁, y, y̅₂, z̅),
    that is, a term must appear inside the inner function in order to flatten it. Likewise,
    strict variants of the Σ expansion rules preclude producing the empty sequence.

    However, it seems more natural to me to allow the solution {x = f(), y=f(a, b)} for the
    matching problem
       ƒ(x,y)≪ᴱƒ(a,b), ƒ is AC
    for example. It isn't clear what the best way to do this is. Feature flag? Generics and
    marker types? Multiple `MatchGenerator`s? For now we use a feature flag.
  */
  // Todo: Determine the "right" way to have different variants of associativity.

  #[cfg(not(feature = "strict-associativity"))]
  /// Have we produced the empty sequence as the first result yet?
  empty_produced: bool,
  /// A `Sequence`, holds the terms of the ground that we have attempted to match
  /// against so far.
  ground_sequence: Sequence,

}

impl MatchGenerator for RuleSVEF {
  fn match_equation(&self) -> MatchEquation {
    self.dfe.match_equation.clone()
  }
}

impl Iterator for RuleSVEF {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {

    // If we haven't produced the empty sequence, do that.
    #[cfg(not(feature = "strict-associativity"))]
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
    Some(self.make_next())
  }
}

impl RuleSVEF {
  pub fn new(me: MatchEquation) -> RuleSVEF {
    RuleSVEF{
      dfe            : DestructuredFunctionEquation::new(&me).unwrap(),
      ground_sequence: Sequence::default(),
      // Se note in the struct definition.
      #[cfg(not(feature = "strict-associativity"))]
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
    if dfe.pattern_function.len() > 0
        && dfe.pattern_function.part(0).kind() == ExpressionKind::SequenceVariable
        && dfe.ground_function.len() > 0 {

      Some(
        RuleSVEF {
          dfe            : dfe.clone(),
          #[cfg(not(feature = "strict-associativity"))]
          empty_produced : false,
          ground_sequence: Sequence::default()
        }
      )

    } else {
      None
    }
  }

}



#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    atoms::{
      SequenceVariable,
      Symbol,
      Function,
      Variable
    },
    expression::RcExpression
  };


  #[test]
  fn generate_rule_svef() {
    let x: RcExpression = Rc::new(SequenceVariable::from("x").into());
    let mut rest = ["u", "v", "w"].iter().map(|&n| Rc::new(Symbol::from(n).into())).collect::<Vec<RcExpression>>();
    let mut f = Function::with_symbolic_head("ƒ");

    f.push(x);
    f.children.append(&mut rest);

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

      #[cfg(not(feature = "strict-associativity"))]
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b, c❩",
      #[cfg(not(feature = "strict-associativity"))]
      "«x»→()", // Not allowed by strict-associativity.

      "ƒ❨u, v, w❩ ≪ ƒ❨b, c❩",
      "«x»→a",
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
    f.children.append(&mut rest);

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
