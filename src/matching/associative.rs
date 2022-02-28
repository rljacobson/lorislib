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

use crate::expression::Expression;

use super::{
  match_generator::{
    MatchGenerator,
    MaybeNextMatchResult,
    NextMatchResult,
    NextMatchResultList
  },
  MatchEquation,
  free_functions::{
    RuleDecF,
    RuleSVEF
  },
  function_application::{
    AFAGenerator,
    EnumerateAll,
    RuleSVE
  }, destructure::DestructuredFunctionEquation
};

/// Rule Dec-A is the same as rule Dec-F.
/// Decomposition under associative head
///   ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)}
/// where ƒ is associative but non-commutative
/// and s∉Ꮙₛₑ.
pub type RuleDecA = RuleDecF;

// Sequence variable elimination under associative head
//    ƒ(x̅,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₂)},
// where ƒ is associative and non-commutative and S={x̅≈(t̃₁)[ƒ]}.
pub type RuleSVEA = RuleSVE<AFAGenerator<EnumerateAll>>;

/// Function variable elimination under associative head
/// ƒ(X(s̃₁),s̃₁)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is associative and non-commutative and S={X≈ƒ}.
pub struct RuleFVEA {
  match_equation: MatchEquation,
  exhausted: bool
}

impl RuleFVEA {
  pub fn new(match_equation: MatchEquation) -> RuleFVEA {
    RuleFVEA{
      match_equation,
      exhausted: false
    }
  }

  pub fn try_rule(dfe: &DestructuredFunctionEquation) -> Option<Self> {
    todo!();
  }

}

impl MatchGenerator for RuleFVEA {
    fn match_equation(&self) -> MatchEquation {
        self.match_equation.clone()
    }
}

impl Iterator for RuleFVEA {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    // One shot.
    if self.exhausted {
      return None;
    }
    self.exhausted = true;
    // This method more than most others demonstrates how we do not verify that the form of these expressions is correct.
    // That verification is done at the time of rule selection.

    let dfe = DestructuredFunctionEquation::new(self.match_equation.clone());

    // Make substitution.
    // Need to splice children of X(s̃₁) into ƒ(s̃₂).
    let (function_variable, new_pattern) =
      if let Expression::Function(function) = dfe.pattern_first.as_ref() {
        let function_variable = function.head.clone();
        let mut new_pattern = dfe.ground_function.duplicate_head(); // f()
        new_pattern.children = function.children.clone(); // f(s̃₁)

        // Now destructure ƒ(s̃₂) to get s̃₂
        let remaining_children = // the value of this if
        if let Expression::Function(fs2) = dfe.pattern_rest.as_ref() {
          fs2.children.clone()
        } else {
          unreachable!();
        };
        new_pattern.children.extend(remaining_children); // ƒ(s̃₁,s̃₂)

        (function_variable, new_pattern)
    } else {
      unreachable!();
    };

    let ground_function_head = dfe.ground_function.head.clone();
    let new_substitution = NextMatchResult::sub(function_variable, ground_function_head);

    // Make new pattern
    // let mut new_pattern = if let Expression::Function(function) = dfe.pattern_rest.as_ref() {
    //   function.children.insert(0, function_first);
    //   function.clone()
    // } else {
    //   unreachable!();
    // };

    let new_match_equation = NextMatchResult::eq(Rc::new(new_pattern.into()), dfe.match_equation.ground.clone());

    Some(smallvec![new_substitution, new_match_equation])
  }
}



/// Individual variable elimination under associative head
///   ƒ(x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₂)},
/// where ƒ is associative and non-commutative and S = {x≈ƒ(t̃₁)}.
/// Since this is almost identical to `RuleSVEF`, we just use
/// RuleSVEF behind the scenes.
pub struct RuleIVEA {
  rule_svef: RuleSVEF,
}

impl MatchGenerator for RuleIVEA {
  fn match_equation(&self) -> MatchEquation {
    self.rule_svef.match_equation()
  }
}

impl Iterator for RuleIVEA {
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    let result = self.rule_svef.next();
    if result.is_none() {
      return None;
    }
    let mut result = result.unwrap();

    let me = self.rule_svef.match_equation();


    // Destructure pattern to get head.
    let new_substitution =
    if let Expression::Function(function) = me.pattern.as_ref() {
      let mut ground_function = function.duplicate_head();

      // Destructure result to get substitution.
      if let NextMatchResult::Substitution(substitution) = result.pop().unwrap() {
        // let substitution_ground = substitution.ground.clone();
        // Destructure sequence in the ground expression
        let children = if let Expression::Sequence(sequence) = substitution.ground.as_ref() {
          sequence.children.clone()
        } else{
          unreachable!();
        };
        ground_function.children = children;

        NextMatchResult::sub(substitution.variable, Rc::new(ground_function.into()))
      } else {
        unreachable!();
      }

    } else {
      unreachable!();
    }; // end new_substitution

    result.push(new_substitution);

    Some(result)
  }
}

impl RuleIVEA {
  pub fn new(me: MatchEquation) -> RuleIVEA {
    RuleIVEA{
      rule_svef: RuleSVEF::new(me)
    }
  }

  pub fn try_rule(dfe: &DestructuredFunctionEquation) -> Option<Self> {
    todo!();
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
  fn generate_rule_svea() {
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
    let rule_svea = RuleSVEA::new(me);

    let result = rule_svea.flatten().map(|r| r.to_string()).collect::<Vec<String>>();
    let expected = [
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b, c❩",
      "«x»→()",
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c❩",
      "«x»→(ƒ❨a❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(a, b)",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(ƒ❨a❩, b)",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(a, ƒ❨b❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(ƒ❨a❩, ƒ❨b❩)",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "«x»→(ƒ❨a, b❩)",
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
      "«x»→(ƒ❨a, b, c❩)"
    ];

    assert_eq!(expected, result.as_slice());

  }


  #[test]
  fn generate_rule_fvea() {
    let mut x = Function::with_variable_head("X");
    x.children = ["u", "v", "w"].iter().map(|&n| Rc::new(Symbol::from(n).into())).collect::<Vec<RcExpression>>();
    let s2 = ["x", "y", "z"].iter().map(|&n| Rc::new(Symbol::from(n).into())).collect::<Vec<RcExpression>>();
    let mut f = Function::with_symbolic_head("ƒ");
    f.push(Rc::new(x.into()));
    f.children.extend(s2);

    let mut g = Function::with_symbolic_head("ƒ");
    g.children = ["a", "b", "c", "d", "e", "h"].iter().map(|&n| Rc::new(Symbol::from(n).into())).collect::<Vec<RcExpression>>();

    let me = MatchEquation{
        pattern: Rc::new(f.into()),
        ground: Rc::new(g.into()),
      };
    let rule_fvea = RuleFVEA::new(me.clone());

    // for result in rule_fvea{
    //   for e in result{
    //     println!("{}", e);
    //   }
    // }

    let expected = [
      "‹X›→ƒ",
      "ƒ❨u, v, w, x, y, z❩ ≪ ƒ❨a, b, c, d, e, h❩"
    ];
    let result = rule_fvea.flatten().map(|r| r.to_string()).collect::<Vec<String>>();

    assert_eq!(expected, result.as_slice());
  }


  #[test]
  fn generate_rule_ivea() {
    let x: RcExpression = Rc::new(Variable::from("x").into());
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

    let rule_ivea = RuleIVEA::new(me);

    // for result in rule_ivea{
    //   for e in result{
    //     println!("{}", e);
    //   }
    // }

    let expected = [
      "ƒ❨u, v, w❩ ≪ ƒ❨a, b, c❩",
      "‹x›→ƒ❨❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨b, c❩",
      "‹x›→ƒ❨a❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨c❩",
      "‹x›→ƒ❨a, b❩",
      "ƒ❨u, v, w❩ ≪ ƒ❨❩",
      "‹x›→ƒ❨a, b, c❩",
    ];
    let result = rule_ivea.flatten().map(|r| r.to_string()).collect::<Vec<String>>();
    assert_eq!(expected, result.as_slice());
  }
}
