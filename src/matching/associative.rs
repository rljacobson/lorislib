/*!

These rules apply when ƒ is associative but not commutative.

### Dec-A: Decomposition under associative head

ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)} where ƒ is associative but non-commutative and s∉Ꮙₛₑ.

### SVE-A: Sequence variable elimination under associative head

ƒ(x&#773;,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is associative and non-commutative and S={x&#773;≈(t̃₁)[ƒ]}.

### FVE-A: Function variable elimination under associative head

ƒ(X(s̃₁),s̃₁)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is associative and non-commutative and S={X≈ƒ}.

### IVE-A: Individual variable elimination under associative head

ƒ(x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is associative and non-commutative and S = {x≈ƒ(t̃₁)}.

*/


use std::rc::Rc;
use smallvec::{
  smallvec
};

use crate::{
  atom::{
    Atom,
    SExpression,
  },
  matching::decomposition::{
    Associative,
    RuleDecNonCommutative
  },
};

use super::{
  match_generator::{
    MatchGenerator,
    MaybeNextMatchResult,
    NextMatchResult,
    NextMatchResultList
  },
  MatchEquation,
  free_functions::{
    RuleSVEF
  },
  function_application::{
    AFAGenerator,
    EnumerateAll,
    RuleSVE
  }
};

/// Rule Dec-A is the same as rule Dec-F.
/// Decomposition under associative head
///   ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)}
/// where ƒ is associative but non-commutative
/// and s∉Ꮙₛₑ.
pub type RuleDecA = RuleDecNonCommutative<Associative>;

/// Sequence variable elimination under associative head
///    ƒ(x̅,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₂)},
/// where ƒ is associative and non-commutative and S={x̅≈(t̃₁)[ƒ]}.
pub type RuleSVEA = RuleSVE<AFAGenerator<EnumerateAll>>;

/// Function variable elimination under associative head
/// ƒ(X(s̃₁),s̃₁)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is associative and non-commutative and S={X≈ƒ}.
///
/// Note that `RuleFVEA` automatically chains with `RuleDecA`, because rule Dec-A always applies
/// when rule FVE-A applies.
pub struct RuleFVEA {
  me       : MatchEquation,
  rule_deca: Option<RuleDecA>, // Doubles as a flag to indicate that the rule has been exhausted.
}

impl RuleFVEA {
  pub fn new(match_equation: MatchEquation) -> RuleFVEA {
    // let rule_deca = Some(RuleDecA::new(match_equation.clone()));

    RuleFVEA{
      me       : match_equation,
      rule_deca: None // Doubles as a flag to indicate that the rule has been exhausted.
    }
  }

  pub fn try_rule(me: &MatchEquation) -> Option<Self> {
    if me.pattern.len() > 0
        && SExpression::part(&me.pattern, 1).try_as_function_variable().is_some()
    {
      Some(
        RuleFVEA::new(me.clone())
      )
    } else {
      None
    }
  }

}

impl MatchGenerator for RuleFVEA {
    fn match_equation(&self) -> MatchEquation {
        self.me.clone()
    }
}

impl Iterator for RuleFVEA {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    // `RuleFVEA` itself is just one shot, so we set up the flag to indicate that it has been
    // exhausted by populating the `rule_deca` field.
    if let Some(rule_deca) = &mut self.rule_deca {
      return rule_deca.next();
    } else {
      self.rule_deca = Some(RuleDecA::new(self.me.clone()));
    }


    // This method more than most others demonstrates how we do not verify that the form of these expressions is
    // correct. That verification is done at the time of rule selection.

    // Make substitution.
    // Need to splice children of X(s̃₁) into ƒ(s̃₂).
    let (function_variable, new_pattern) = { // scope of `function`, `remaining_children`

      let function                : Rc<Vec<Atom>> = SExpression::children(&self.me.pattern_first());
      let function_variable       : Atom          = function[0].clone(); //X_
      let mut new_pattern_children: Vec<Atom>     = vec![self.me.ground.head()]; // f()
      new_pattern_children.extend(
        function[1..].iter()
                .cloned()
                .chain(
          // The remaining children, destructured ƒ(s̃₂) to get s̃₂
          SExpression::children(&self.me.pattern)[2..] // Skip the head and the first child
              .iter()
              .cloned() // A "deep" clone.
        )
      );
      let new_pattern = // f(s̃₁)
        Atom::SExpression(Rc::new(new_pattern_children));

      (function_variable, new_pattern)
    };

    let new_substitution =
        NextMatchResult::sub(function_variable, self.me.ground.head());
    let new_match_equation =
        NextMatchResult::eq(
          new_pattern,
          self.me.ground.clone()
        );

    Some(smallvec![new_substitution, new_match_equation])
  }
}



/// Individual variable elimination under associative head
///   ƒ(x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₂)},
/// where ƒ is associative and non-commutative and S = {x≈ƒ(t̃₁)}. Since this is almost identical to
/// `RuleSVEF`, we just use RuleSVEF behind the scenes.
///
/// Note that `RuleIVEA` automatically chains with `RuleDecA`, because rule Dec-A always applies
/// when rule IVE-A applies.
pub struct RuleIVEA {
  rule_svef: RuleSVEF,
  rule_deca: RuleDecA
}

impl MatchGenerator for RuleIVEA {
  fn match_equation(&self) -> MatchEquation {
    self.rule_svef.match_equation()
  }
}

impl Iterator for RuleIVEA {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    // The inner `RuleSVEF` is chained with the inner `RuleDecA`. We can't just use `chain()`,
    // though, because the result of `RuleSVEF` needs to be transformed.
    let mut result =
        match self.rule_svef.next() {
          Some(result) => result,
          None => {
            return self.rule_deca.next()
          }
        };

    // Transform the substitution to be a substitution for a function instead of a sequence.
    let new_substitution = // the value of this if-let
    // Destructure result to get substitution.
    if let NextMatchResult::Substitution(substitution) = result.pop().unwrap() {
      // Destructure substitution to get at ground.
      let (variable, ground) = (substitution.variable, substitution.ground);

      let ground = if let Atom::SExpression(children) = ground {
        SExpression::new_swapped_head(self.rule_svef.match_equation.ground.head(), children.as_ref())
      } else {
        // Not a sequence, just a singleton expression.
        let new_children = vec![self.rule_svef.match_equation.ground.head(), ground];
        Atom::SExpression(Rc::new(new_children))
      };

      NextMatchResult::sub(variable, ground)
    } else {
      unreachable!();
    };

    result.push(new_substitution);

    Some(result)
  }
}

impl RuleIVEA {
  pub fn new(me: MatchEquation) -> RuleIVEA {
    RuleIVEA{
      rule_svef: RuleSVEF::new(me.clone()),
      rule_deca: RuleDecA::new(me)
    }
  }

  pub fn try_rule(me: &MatchEquation) -> Option<Self> {
    // Pattern: f[‹x›,…]

    if me.pattern.len() > 0
        && SExpression::part(&me.pattern, 1).try_as_variable().is_some()
    {
      Some(
        RuleIVEA::new(me.clone())
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
    }
  };
  use crate::logging::set_verbosity;


  // solve ƒ(x̅,s̃)≪ᴱƒ(t̃₁,t̃₂)
  #[test]
  fn generate_rule_svea() {
    set_verbosity(5);

    let f: Atom = { // Scope of children
      let mut children = vec![
        Symbol::from_static_str("ƒ"),
        SExpression::sequence_variable_static_str("x")
      ];
      children.extend(["u", "v", "w"].iter().map(|&n| Symbol::from_static_str(n)));
      Atom::SExpression(Rc::new(children))
    };

    let g: Atom = Atom::SExpression(Rc::new(
      ["ƒ", "a", "b", "c"].iter().map(|&n| Symbol::from_static_str(n)).collect::<Vec<Atom>>()
    ));

    let me = MatchEquation{
        pattern: f,
        ground: g,
    };
    let rule_svea = RuleSVEA::new(me);

    let result = rule_svea.flatten().map(|r| r.to_string()).collect::<Vec<String>>();
    let expected = [
      #[cfg(not(feature = "strict-associativity"))]
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b, c❩",
      #[cfg(not(feature = "strict-associativity"))]
      "«x»→()",
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c❩",
      "«x»→a",
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c❩",
      "«x»→ƒ❨a❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(a, b)",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(ƒ❨a❩, b)",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(a, ƒ❨b❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(ƒ❨a❩, ƒ❨b❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→ƒ❨a, b❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(a, b, c)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(ƒ❨a❩, b, c)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(a, ƒ❨b❩, c)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(ƒ❨a❩, ƒ❨b❩, c)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(a, b, ƒ❨c❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(ƒ❨a❩, b, ƒ❨c❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(a, ƒ❨b❩, ƒ❨c❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(ƒ❨a❩, ƒ❨b❩, ƒ❨c❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(ƒ❨a, b❩, c)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(ƒ❨a, b❩, ƒ❨c❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(a, ƒ❨b, c❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→(ƒ❨a❩, ƒ❨b, c❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "«x»→ƒ❨a, b, c❩"
    ];

    assert_eq!(expected, result.as_slice());

  }

  /// Solve ƒ❨‹X›❨u, v, w❩, x, y, z❩ ≪ ƒ❨a, b, c, d, e, h❩
  #[test]
  fn generate_rule_fvea() {

    let w = { // scope of children
      let mut children = vec![SExpression::variable_static_str("X")];
      children.extend(["u", "v", "w"].iter().map(|&n| Symbol::from_static_str(n)));
      Atom::SExpression(Rc::new(children))
    };
    let f = { // scope of children
      let mut children = vec![
        Symbol::from_static_str("ƒ"),
        w
      ];
      children.extend(
        ["x", "y", "z"].iter().map(|&n| Symbol::from_static_str(n))
      );
      Atom::SExpression(Rc::new(children))
    };

    let g = Atom::SExpression(Rc::new(
      ["ƒ", "a", "b", "c", "d", "e", "h"]
                      .iter()
                      .map(|n| Symbol::from_static_str(n))
                      .collect::<Vec<Atom>>()
    ));

    let me = MatchEquation{
        pattern: f,
        ground: g,
      };
    let rule_fvea = RuleFVEA::new(me);

    // for result in rule_fvea{
    //   for e in result{
    //     println!("{}", e);
    //   }
    // }

    let expected = [
      "‹X›→ƒ",
      "ƒ❨u, v, w, x, y, z❩ ≪ ƒ❨a, b, c, d, e, h❩",
      "‹X›❨u, v, w❩ ≪ a",
      "ƒ❨x, y, z❩ ≪ ƒ❨b, c, d, e, h❩"
    ];
    let result = rule_fvea.flatten().map(|r| r.to_string()).collect::<Vec<String>>();

    assert_eq!(expected, result.as_slice());
  }


  /// Solve ƒ❨‹x›, u, v, w❩ ≪ ƒ❨a, b, c❩
  #[test]
  fn generate_rule_ivea() {
    let f: Atom = {
      let mut children = vec![
        Symbol::from_static_str("ƒ"),
        SExpression::variable_static_str("x")
      ];
      children.extend(
        ["u", "v", "w"].iter().map(|&n| Symbol::from_static_str(n))
      );
      Atom::SExpression(Rc::new(children))
    };

    let g = Atom::SExpression(Rc::new(
      ["ƒ", "a", "b", "c"]
          .iter()
          .map(|n| Symbol::from_static_str(n))
          .collect::<Vec<Atom>>()
    ));

    let me = MatchEquation{
        pattern: f,
        ground: g,
    };

    let rule_ivea = RuleIVEA::new(me);

    // for result in rule_ivea{
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
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "‹x›→ƒ❨a, b❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "‹x›→ƒ❨a, b, c❩",
      "‹x› ≪ a",
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c❩"
    ];
    let result = rule_ivea.flatten().map(|r| r.to_string()).collect::<Vec<String>>();
    assert_eq!(expected, result.as_slice());
  }
}
