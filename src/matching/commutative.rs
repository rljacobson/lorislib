/*!

These rules apply when f is commutative but not associative.

### Dec-C: Decomposition under commutative head

ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)} where ƒ is commutative but non-associative and s∉Ꮙₛₑ.

### SVE-C: Sequence variable elimination under commutative head

ƒ(x&#773;,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)} where n ≥ 0, ƒ is commutative and
non-associative, and S = {x&#773; ≈ ❴t₁,…,tₙ❵ }.

*/

use std::rc::Rc;

use smallvec::smallvec;
use permutation_generator::PermutationGenerator32 as Permutations;

use crate::{
  atoms::Sequence,
  expression::ExpressionKind,
  matching::decomposition::{
    NonAssociative,
    RuleDecCommutative
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
  }
};

pub type RuleDecC = RuleDecCommutative<NonAssociative>;

pub struct RuleSVEC {
  dfe: DestructuredFunctionEquation,
  /// Bit positions indicate which subset of the ground's children are currently
  /// being matched against. You'd be crazy to try to match against all
  /// subsets of a set with more than 32 elements. We use `u32::MAX` ==
  /// `2^32-1` to indicate the rule is exhausted, so we only support at most
  /// 31 children.
  subset: u32,
  permutations: Permutations
}


impl RuleSVEC {
  pub fn new(me: MatchEquation) -> RuleSVEC {
    RuleSVEC{
      dfe         : DestructuredFunctionEquation::new(&me).unwrap(),
      #[cfg(feature = "strict-associativity")]      // Skip the empty subset
      subset      : 1,
      #[cfg(not(feature = "strict-associativity"))] // Include the empty subset
      subset      : 0,
      permutations: Permutations::new(1).unwrap()
    }
  }

  pub fn try_rule(dfe: &DestructuredFunctionEquation) -> Option<Self> {
    if dfe.pattern_function.len() > 0
        && dfe.pattern_function.part(0).kind() == ExpressionKind::SequenceVariable
        && dfe.ground_function.len() > 0 {

      Some(
        RuleSVEC {
          dfe         : dfe.clone(),
          #[cfg(feature = "strict-associativity")]      // Skip the empty subset
          subset      : 1,
          #[cfg(not(feature = "strict-associativity"))] // Include the empty subset
          subset      : 0,
          permutations: Permutations::new(1).unwrap(),
        }
      )

    } else {
      None
    }
  }

}


impl Iterator for RuleSVEC {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    let mut n = self.dfe.ground_function.len();
    n = if n > 31 { 31 } else { n };
    let max_subset_state: u32 = ((1 << n) - 1) as u32;


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
    // Have we sent the empty subset yet?
    #[cfg(not(feature = "strict-associativity"))]
    if self.subset == 0 {
      self.subset += 1;
      self.permutations = Permutations::new(1).unwrap();
      let substitution = NextMatchResult::sub(
        self.dfe.pattern_first.clone(),
        Rc::new(Sequence::default().into())
      );
      let match_equation = NextMatchResult::eq(
        self.dfe.pattern_rest.clone(),
        self.dfe.match_equation.ground.clone(),
      );
      return Some(
        smallvec![
          match_equation,
          substitution
        ]
      );
    }


    let permutation = // the value of this match
    match self.permutations.next() {

      None => {
        // Exhausted the permutations for this subset. Create a new
        // subset and start matching its permutations.
        if self.subset == max_subset_state {
          // This generator is exhausted.
          return None;
        }

        // This is the only place self.subset is updated.
        self.subset += 1;
        self.permutations = Permutations::new(self.subset.count_ones() as u8).unwrap();
        self.permutations.next().unwrap()
      }

      Some(permutation) => {
        permutation
      }

    };

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
    let ordered_children = permutation.map(|idx| subset[idx as usize].clone()).collect::<Vec<_>>();

    let substitution = NextMatchResult::sub(
      self.dfe.pattern_first.clone(),
      Rc::new(Sequence::from_children(ordered_children).into())
    );

    let mut new_ground_function = self.dfe.ground_function.duplicate_head();
    new_ground_function.children = complement;

    let match_equation = NextMatchResult::eq(
      self.dfe.pattern_rest.clone(),
      Rc::new(new_ground_function.into()),
    );

    Some(
      smallvec![
        match_equation,
        substitution
      ]
    )
  }
}


impl MatchGenerator for RuleSVEC {
  fn match_equation(&self) -> MatchEquation {
    self.dfe.match_equation.clone()
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
  fn generate_rule_svec() {
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

    let rule_svec = RuleSVEC::new(me);

    // for result in rule_svec {
    //   for e in result{
    //     println!("{}", e);
    //   }
    // }
    let result = rule_svec.flatten().map(|r| r.to_string()).collect::<Vec<String>>();
    let expected = [
      #[cfg(not(feature = "strict-associativity"))]
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b, c❩",
      #[cfg(not(feature = "strict-associativity"))]
      "«x»→()", // Not allowed by strict-associativity.
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c❩",
      "«x»→a",
      "ƒ❨u, v, w❩ ≪ ƒ❨a, c❩",
      "«x»→b",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(a, b)",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(b, a)",
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b❩",
      "«x»→c",
      "ƒ❨u, v, w❩ ≪ ƒ❨b❩",
      "«x»→(a, c)",
      "ƒ❨u, v, w❩ ≪ ƒ❨b❩",
      "«x»→(c, a)",
      "ƒ❨u, v, w❩ ≪ ƒ❨a❩",
      "«x»→(b, c)",
      "ƒ❨u, v, w❩ ≪ ƒ❨a❩",
      "«x»→(c, b)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(a, b, c)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(a, c, b)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(b, a, c)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(b, c, a)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(c, a, b)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(c, b, a)",
    ];

    assert_eq!(expected, result.as_slice());

  }

  #[test]
  fn generate_rule_decc() {
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
    let rule_decc = RuleDecC::new(me);

    // for result in rule_decc {
    //   for e in result{
    //     println!("{}", e);
    //   }
    // }

    let expected = [
      "‹s› ≪ a",
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c, d❩",
      "‹s› ≪ b",
      "ƒ❨u, v, w❩ ≪ ƒ❨a, c, d❩",
      "‹s› ≪ c",
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b, d❩",
      "‹s› ≪ d",
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b, c❩",
    ];
    let result = rule_decc.flatten().map(|r| r.to_string()).collect::<Vec<String>>();

    assert_eq!(expected, result.as_slice());

  }

}
