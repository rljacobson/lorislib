/*!
Rules for free symbols.
These rules apply when ƒ is free.

Dec-F: Decomposition under free head ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)}, where ƒ is free and s∉Ꮙₛₑ.

SVE-F: Sequence variable elimination under free head ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is free and S={x̅≈t̃₁}. An SVE-F match generator must enumerate all possible ways of choosing t̃₁.

*/


use std::rc::Rc;
use smallvec::{
  smallvec,
};

use crate::{
  atom::{
    Atom,
    SExpression,
  },
  matching::decomposition::{
    NonAssociative,
    RuleDecNonCommutative
  }
};

use super::{
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

type Sequence = Vec<Atom>;

// ƒ(x̅,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is free and S={x̅≈t̃₁}
pub struct RuleSVEF {
  pub(crate) match_equation: MatchEquation,

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

  #[cfg(not(feature = "strict_associativity"))]
  /// Have we produced the empty sequence as the first result yet?
  empty_produced: bool,
  /// A `Sequence`, holds the terms of the ground that we have attempted to match
  /// against so far.
  ground_sequence: Sequence,

}

impl MatchGenerator for RuleSVEF {
  fn match_equation(&self) -> MatchEquation {
    self.match_equation.clone()
  }
}

impl Iterator for RuleSVEF {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {

    // If we haven't produced the empty sequence, do that.
    #[cfg(not(feature = "strict_associativity"))]
    if !self.empty_produced {
      self.empty_produced = true;
      return Some(self.make_next());
    }

    // Are there any more terms to take?
    if self.match_equation.ground.len() == self.ground_sequence.len() {
      // No more terms.
      return None;
    }

    // Take the next term from the ground function.
    self.ground_sequence.push(
      SExpression::part(
        &self.match_equation.ground,
        self.ground_sequence.len()+1 // skip the head
      )
    );

    // Construct the result.
    Some(self.make_next())
  }
}

impl RuleSVEF {
  pub fn new(me: MatchEquation) -> RuleSVEF {
    RuleSVEF{
      match_equation: me,
      ground_sequence: Vec::new(),
      // Se note in the struct definition.
      #[cfg(not(feature = "strict_associativity"))]
      empty_produced : false
    }
  } // end new RuleSVEF

  // Constructs the next result using components of `self`.
  fn make_next(&self) -> NextMatchResultList {

    let match_equation_ground = { // scope of extras
      let mut match_equation_ground_children = vec![self.match_equation.ground.head()];
      match_equation_ground_children.extend(
        // Todo: Does this do the right thing when `ground_function.len()==ground_sequence.len()`?
        SExpression::children(&self.match_equation.ground)[self.ground_sequence.len()+1..].iter().cloned()
      );
      Atom::SExpression(Rc::new(match_equation_ground_children))
    };

    let result_equation =
      NextMatchResult::MatchEquation(
        MatchEquation{
          pattern: self.match_equation.pattern_rest(),
          ground: match_equation_ground
        }
      );

    let result_substitution = NextMatchResult::Substitution(
      Substitution{
        variable: self.match_equation.pattern_first(),
        ground: SExpression::sequence(self.ground_sequence.clone()),
      }
    );

    return smallvec![result_equation, result_substitution];
  }


  pub fn try_rule(me: &MatchEquation) -> Option<Self> {
    if me.pattern.len() > 0
        && SExpression::part(&me.pattern, 1).is_sequence_variable().is_some()
        // && me.ground.len() > 0
    {

      Some(
        RuleSVEF::new(me.clone())
      )

    } else {
      None
    }
  }

}



#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use super::*;
  use crate::{
    atom::{
      Atom,
      SExpression,
      Symbol
    },
  };



  #[test]
  fn generate_rule_svef() {
    let f = { // scope of children
      let mut children = vec![
        Symbol::from_static_str("ƒ"),
        SExpression::sequence_variable_static_str("x")
      ];
      let mut rest = ["u", "v", "w"].iter()
                                    .map(|&n| Symbol::from_static_str(n))
                                    .collect::<Vec<Atom>>();
      children.append(&mut rest);
      Atom::SExpression(Rc::new(children))
    };

    let g = { // scope of children
      let children = ["ƒ", "a", "b", "c"].iter().map(|&n| Symbol::from_static_str(n)).collect::<Vec<Atom>>();
      Atom::SExpression(Rc::new(children))
    };

    let me = MatchEquation{
      pattern: f,
      ground : g,
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

      #[cfg(not(feature = "strict_associativity"))]
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b, c❩",
      #[cfg(not(feature = "strict_associativity"))]
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

  // Solve f(‹s›, u, v, w) << f(a, b, c, d)
  #[test]
  fn generate_rule_decf() {
    let f = { // scope of children, rest
      let mut children = vec![
        Symbol::from_static_str("ƒ"),
        SExpression::variable_static_str("s")
      ];
      let mut rest = ["u", "v", "w"].iter()
                                    .map(|&n| Symbol::from_static_str(n))
                                    .collect::<Vec<Atom>>();
      children.append(&mut rest);
      Atom::SExpression(Rc::new(children))
    };

    let g = { // scope of children
      let children = ["ƒ", "a", "b", "c", "d"].iter()
                                                  .map(|&n| Symbol::from_static_str(n))
                                                  .collect::<Vec<Atom>>();
      Atom::SExpression(Rc::new(children))
    };

    let me = MatchEquation{
      pattern: f,
      ground : g,
    };
    let rule_decf: RuleDecNonCommutative<NonAssociative> = RuleDecF::new(me);

    let expected = [
      "‹s› ≪ a",
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c, d❩"
    ];
    let result = rule_decf.flatten().map(|r| r.to_string()).collect::<Vec<String>>();

    assert_eq!(expected, result.as_slice());

  }

}
