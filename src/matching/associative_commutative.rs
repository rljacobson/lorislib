/*!

## *Rules for associative-commutative symbols*.

These rules apply when ƒ is both associative and commutative.

### Dec-AC: Decomposition under AC head

ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)} where ƒ is
associative-commutative and s∉Ꮙₛₑ.

### SVE-AC: Sequence variable elimination under AC head

ƒ(x&#773;,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁)
  ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)} where n ≥ 0, ƒ is
associative-commutative, and S = {x&#773; ≈ ❴t₁,…,tₙ❵[ƒ] }.

### FVE-AC: Function variable elimination under AC head

ƒ(X(s̃₁),s̃₁)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is
associative-commutative and S={X≈ƒ}.

*/


use std::cmp::min;
use smallvec::smallvec;
use crate::{
  matching::{
    decomposition::{
      Associative,
      RuleDecCommutative
    },
    MatchEquation,
    match_generator::{
      MatchGenerator,
      MaybeNextMatchResult,
      NextMatchResult,
      NextMatchResultList
    }
  },
  atom::SExpression,
};
#[allow(unused_imports)]
use crate::logging::{Channel, log};

use super::{
  function_application::{
    AFACGenerator,
    EnumerateAll,
    RuleSVE
  },
  associative::RuleFVEA
};

/// Dec-AC: Decomposition under AC head
/// ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)}
/// where ƒ is associative-commutative and s∉Ꮙₛₑ.
/// Identical to `RuleDecC`, decomposition under commutative head.
pub type RuleDecAC = RuleDecCommutative<Associative>;

/// Sequence variable elimination under AC head
/// ƒ(x̅,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ
///   {ƒ(s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)}
/// where n ≥ 0, ƒ is associative-commutative, and
///   S = {x̅ ≈ ❴t₁,…,tₙ❵[ƒ] }.
pub type RuleSVEAC = RuleSVE<AFACGenerator<EnumerateAll>>;

/// Function variable elimination under AC head
/// ƒ(X(s̃₁),s̃₁)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ
/// is associative-commutative and S={X≈ƒ}.
/// Same as `RuleFVEA`.
///
/// Note that `RuleFVEAC` automatically chains with `RuleDecAC`, because rule Dec-AC always applies
/// when rule FVE-AC applies.
pub type RuleFVEAC = RuleFVEA;


/// IVE-AC: Individual variable elimination under AC head.
///
/// Note that `RuleIVEAC` automatically chains with `RuleDecAC`, because rule Dec-AC always applies
/// when rule IVE-AC applies.
pub struct RuleIVEAC {
  match_equation: MatchEquation,
  /// Bit positions indicate which subset of the ground's children are currently
  /// being matched against. You'd be crazy to try to match against all
  /// subsets of a set with more than 32 elements. We use `u32::MAX` ==
  /// `2^32-1` to indicate the rule is exhausted, so we only support at most
  /// 31 children.
  subset: u32,
  rule_decac: RuleDecAC
}

impl RuleIVEAC {
  /// Create a new `RuleIVEAC`.
  pub fn new(me: MatchEquation) -> Self {
    RuleIVEAC {
      match_equation: me.clone(),
      #[cfg(not(feature = "strict-associativity"))]
      subset: 0,
      #[cfg(feature = "strict-associativity")]
      subset: 1, // Cannot match the empty set under strict associativity.
      rule_decac: RuleDecAC::new(me)
    }
  }

  pub fn try_rule(me: &MatchEquation) -> Option<RuleIVEAC> {

    if me.pattern.len() > 0
        && SExpression::part(&me.pattern, 1).try_as_variable().is_some()
    {
      // Additional condition for strict associativity
      #[cfg(feature = "strict-associativity")]
      if me.ground.len() == 0 {
        return None;
      }

      Some(
        RuleIVEAC::new(me.clone())
      )
    } else {
      None
    }
  }
}

impl MatchGenerator for RuleIVEAC {
  fn match_equation(&self) -> MatchEquation {
    self.match_equation.clone()
  }
}


impl Iterator for RuleIVEAC {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    let n = min(32, self.match_equation.ground.len());
    let max_subset_state: u32 = ((1 << n) - 1) as u32;

    if self.subset > max_subset_state {
      return self.rule_decac.next();
    }

    // For the subset of the children that will be matched against as well as its
    // complement, which will go in the new match equation.
    let mut subset = vec![];
    let mut complement = vec![];
    let ground_children = SExpression::children(&self.match_equation.ground);
    let mut child_iter = ground_children.iter();
    // Skip the head
    child_iter.next();
    for (k, c) in child_iter.enumerate(){
      if k == 32 {
        break;
      }
      if ((1 << k) as u32 & self.subset) != 0 {
        subset.push(c.clone());
      } else {
        complement.push(c.clone());
      }
    }

    let new_function = SExpression::new(self.match_equation.ground.head(), subset);
    let substitution = NextMatchResult::sub(
      self.match_equation.pattern_first(),
      new_function
    );
    let new_ground_function = SExpression::new(self.match_equation.ground.head(), complement);

    let match_equation = NextMatchResult::eq(
      self.match_equation.pattern_rest(),
      new_ground_function,
    );

    self.subset += 1;

    Some(
      smallvec![
        match_equation,
        substitution
      ]
    )
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


  /// Solve ƒ❨‹x›, u, v, w❩ ≪ ƒ❨a, b, c❩
  #[test]
  fn generate_rule_ivea() {

    let f = {
      let mut children = vec![
        Symbol::from_static_str("ƒ"),
        SExpression::variable_static_str("x"),
      ];
      let mut rest = ["u", "v", "w"].iter().map(|&n| Symbol::from_static_str(n)).collect::<Vec<Atom>>();
      children.append(&mut rest);
      Atom::SExpression(Rc::new(children))
    };

    let g = {
      let children = ["ƒ", "a", "b", "c"].iter().map(|&n| Symbol::from_static_str(n)).collect::<Vec<Atom>>();
      Atom::SExpression(Rc::new(children))
    };

    let me = MatchEquation{
      pattern: f,
      ground: g,
    };

    let rule_iveac = RuleIVEAC::new(me);

    // for result in rule_iveac {
    //   for e in result{
    //     println!("{}", e);
    //   }
    // }

    // All (single-step) solutions to ƒ❨‹x›, u, v, w❩ ≪ ƒ❨a, b, c❩
    let expected = [
      #[cfg(not(feature = "strict-associativity"))]
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b, c❩",
      #[cfg(not(feature = "strict-associativity"))]
      "‹x›→ƒ❨❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c❩",
      "‹x›→ƒ❨a❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨a, c❩",
      "‹x›→ƒ❨b❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "‹x›→ƒ❨a, b❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b❩",
      "‹x›→ƒ❨c❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨b❩",
      "‹x›→ƒ❨a, c❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨a❩",
      "‹x›→ƒ❨b, c❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "‹x›→ƒ❨a, b, c❩",
      "‹x› ≪ a",
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c❩",
      "‹x› ≪ b",
      "ƒ❨u, v, w❩ ≪ ƒ❨a, c❩",
      "‹x› ≪ c",
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b❩"
    ];

    let result = rule_iveac.flatten().map(|r| r.to_string()).collect::<Vec<String>>();
    assert_eq!(expected, result.as_slice());
  }
}
