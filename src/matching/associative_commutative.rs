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


use std::rc::Rc;
use smallvec::smallvec;
use crate::{
  matching::{
    decomposition::{
      Associative,
      RuleDecCommutative
    },
    destructure::DestructuredFunctionEquation,
    MatchEquation,
    match_generator::{
      MatchGenerator,
      MaybeNextMatchResult,
      NextMatchResult,
      NextMatchResultList
    }
  },
  expression::ExpressionKind,
};
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
  dfe: DestructuredFunctionEquation,
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
      dfe: DestructuredFunctionEquation::new(&me).unwrap(),
      #[cfg(not(feature = "strict-associativity"))]
      subset: 0,
      #[cfg(feature = "strict-associativity")]
      subset: 1, // Cannot match the empty set under strict associativity.
      rule_decac: RuleDecAC::new(me)
    }
  }

  pub fn try_rule(dfe: &DestructuredFunctionEquation) -> Option<RuleIVEAC> {
    if dfe.pattern_function.len() > 0
        && dfe.pattern_function.part(0).kind() == ExpressionKind::Variable
    {
      // Additional condition for strict associativity
      #[cfg(feature = "strict-associativity")]
      if dfe.ground_function.len() == 0{
        return None;
      }

      Some(
        RuleIVEAC {
          dfe: dfe.clone(),
          #[cfg(not(feature = "strict-associativity"))]
          subset: 0,
          #[cfg(feature = "strict-associativity")]
          subset: 1, // Cannot match the empty set under strict associativity.
          rule_decac: RuleDecAC::new(dfe.match_equation.clone())
        }
      )
    } else {
      None
    }
  }
}

impl MatchGenerator for RuleIVEAC {
  fn match_equation(&self) -> MatchEquation {
    self.dfe.match_equation.clone()
  }
}


impl Iterator for RuleIVEAC {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    let mut n = self.dfe.ground_function.len();
    n = if n > 31 { 31 } else { n };
    let max_subset_state: u32 = ((1 << n) - 1) as u32;

    if self.subset > max_subset_state {
      return self.rule_decac.next();
    }

    // For the subset of the children that will be matched against as well as its
    // complement, which will go in the new match equation.
    let mut subset = vec![];
    let mut complement = vec![];
    for (k, c) in self.dfe.ground_function.children.iter().enumerate(){
      if k == 31 {
        break;
      }
      if ((1 << k) as u32 & self.subset) != 0 {
        subset.push(c.clone());
      } else {
        complement.push(c.clone());
      }
    }

    let mut new_function = self.dfe.ground_function.duplicate_head();
    new_function.children = subset;

    let substitution = NextMatchResult::sub(
      self.dfe.pattern_first.clone(),
      Rc::new(new_function.into())
    );

    let mut new_ground_function = self.dfe.ground_function.duplicate_head();
    new_ground_function.children = complement;

    let match_equation = NextMatchResult::eq(
      self.dfe.pattern_rest.clone(),
      Rc::new(new_ground_function.into()),
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
  use super::*;
  use crate::{
    atoms::{
      Symbol,
      Function, Variable
    },
    expression::RcExpression
  };


  /// Solve ƒ❨‹x›, u, v, w❩ ≪ ƒ❨a, b, c❩
  #[test]
  fn generate_rule_ivea() {
    let x: RcExpression = Rc::new(Variable::from("x").into());
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

    let rule_iveac = RuleIVEAC::new(me);

    // for result in rule_iveac {
    //   for e in result{
    //     println!("{}", e);
    //   }
    // }

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
