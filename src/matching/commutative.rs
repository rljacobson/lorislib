/*!

These rules apply when f is commutative but not associative.

### Dec-C: Decomposition under commutative head

ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)} where ƒ is commutative but non-associative and s∉Ꮙₛₑ.

### SVE-C: Sequence variable elimination under commutative head

ƒ(x&#773;,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)} where n ≥ 0, ƒ is commutative and
non-associative, and S = {x&#773; ≈ ❴t₁,…,tₙ❵ }.

*/

use std::cmp::min;
use smallvec::smallvec;
use permutation_generator::PermutationGenerator32 as Permutations;

use crate::{
  atom::SExpression,
  matching::decomposition::{
    NonAssociative,
    RuleDecCommutative
  }
};

use super::{
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
  match_equation: MatchEquation,
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
      match_equation: me,
      #[cfg(feature = "strict-associativity")]      // Skip the empty subset
      subset      : 1,
      #[cfg(not(feature = "strict-associativity"))] // Include the empty subset
      subset      : 0,
      permutations: Permutations::new(1).unwrap()
    }
  }

  pub fn try_rule(me: &MatchEquation) -> Option<Self> {
    // Patter: f[«x»]
    // Ground: g[a,…]
    if me.pattern.len() > 0
        && SExpression::part(&me.pattern, 1).is_sequence_variable().is_some()
        && me.ground.len() > 0 {
      Some(
        RuleSVEC {
          match_equation: me.clone(),
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
    let n = min(self.match_equation.ground.len(), 31);
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
        self.match_equation.pattern_first(),
        SExpression::empty_sequence()
      );
      let match_equation = NextMatchResult::eq(
        self.match_equation.pattern_rest(),
        self.match_equation.ground.clone(),
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
    let ground_children = SExpression::children(&self.match_equation.ground);
    let mut child_iter = ground_children.iter();
    // Skip the head
    child_iter.next();
    for (k, c) in child_iter.enumerate(){
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
      self.match_equation.pattern_first(),
      SExpression::sequence(ordered_children)
    );

    let new_ground_function = SExpression::new(self.match_equation.ground.head(), complement);
    let match_equation = NextMatchResult::eq(
      self.match_equation.pattern_rest(),
      new_ground_function,
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
    self.match_equation.clone()
  }
}

// todo: I think these tests should fail unless g/f are commutative. Indeed, the rule under test should never fire
//       otherwise.
#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use super::*;
  use crate::{
    atom::{
      Atom,
      SExpression,
      Symbol,
    }
  };

  #[test]
  fn generate_rule_svec() {
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
    let f: Atom = { // scope of children, rest
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

    let g: Atom = { // scope of children
      let children = ["ƒ", "a", "b", "c", "d"].iter()
                                         .map(|&n| Symbol::from_static_str(n))
                                         .collect::<Vec<Atom>>();
      Atom::SExpression(Rc::new(children))
    };

    let me = MatchEquation{
        pattern: f,
        ground : g,
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
