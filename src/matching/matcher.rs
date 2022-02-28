/*!

A `Matcher` holds the state of the matching algorithm as it walks the
expression tree looking for a match. Most importantly, it keeps track of the
substitutions that are currently active.

In terms of Dundua, `Matcher` keeps track of $S$ and $\Gamma$. The set $S$ is
the set of active `Matcher`s. Since future rule applications depend on a `Matcher`'s
choice of how to transform the equation, the set `S` is implemented as a stack.
When a `Matcher` is exhausted, it is popped from the stack, and the next `Matcher` is
queried for the next substitution.

Other state includes whether or not patterns are being held. A subexpression can
be wrapped in `HoldPattern`. Inside of `HoldPattern`, pattern symbols are treated
as literal symbols, not as patterns.

*/

use std::{collections::HashMap, fmt::Display, rc::Rc};

use crate::{
  expression::{
    RcExpression,
    Expression,
    ExpressionKind
  }
};

use super::{
  match_generator::MatchGenerator,
  SolutionSet,
  MatchEquation,
  common::{
    RuleT,
    RuleIVE,
    RuleFVE
  },
  free_functions::{
    RuleDecF,
    RuleSVEF
  }, destructure::DestructuredFunctionEquation, commutative::{RuleDecC, RuleSVEC}
};



/// Items that can be pushed onto the match stack.
#[derive(Clone)]
pub(crate) enum MatchStack {

  /// The match generator responsible for the operations sitting immediately above it on
  /// the stack. Those operations are undone in order to get back to the
  /// match generator to call `next()`.
  MatchGenerator(Rc<dyn MatchGenerator>),

  /// A variable or sequence variable substitution. We only need to record the key
  /// (the expression) of the `SolutionSet` hashmap.
  Substitution(RcExpression),

  /// An operation representing pushing matching equations onto the equation stack.
  ProducedMatchEquations(u32),

}


impl MatchStack {

  /// Wraps the given `MatchGenerator`.
  pub fn rule(generator: Rc<dyn MatchGenerator>) -> MatchStack {
    MatchStack::MatchGenerator(generator)
  }

}


/// Holds the state of the in-process pattern matching attempt.
pub struct Matcher {
  /// The match_stack is where operations that change the state are recorded.
  /// Operations are pushed when they are done and popped when they are undone.
  match_stack: Vec<MatchStack>,
  /// The match equations that still need to be solved.
  equation_stack: Vec<MatchEquation>,
  /// The symbol table recording all veriable/sequence variable bindings.
  substitutions: SolutionSet,
}


impl Display for Matcher {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let equations = self.equation_stack
                        .iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<String>>()
                        .join(", ");
    let substitutions = self.substitutions
                            .iter()
                            .map(|(k, v)| format!("{}→{}", k, v))
                            .collect::<Vec<String>>()
                            .join(", ");
    write!(f, "Γ={{{}}}\nS={{{substitutions}}}", equations)
  }
}


impl Matcher {

  /// Create a new `Matcher` for the match equation `pattern`≪`subject`.
  pub fn new(pattern: RcExpression, subject: RcExpression) -> Matcher {
    Matcher {
      match_stack: Vec::new(),
      equation_stack: vec![MatchEquation{pattern, ground: subject}],
      substitutions: HashMap::new(),
    }
  }


  /// Pushes the given `MatchGenerator`.
  pub fn push_rule(&mut self, generator: Rc<dyn MatchGenerator>) {
    self.match_stack.push(MatchStack::MatchGenerator(generator));
  }


  /// Undoes the effects of the last call to `next()` and, for convenience, returns
  /// the responsible match generator in the form of an `Rc<Matcher>` object.
  /// Upon return the `Matcher` will be active, i.e. on top of the match
  /// stack.
  fn undo(&mut self) -> Rc<dyn MatchGenerator> {
    loop {
      match self.match_stack.last().unwrap().clone() {

        MatchStack::MatchGenerator(match_generator) => {
          // Leave the match generator on top of the match stack.
          return match_generator.clone();
        },

        MatchStack::Substitution(expression) => {
          // Remove it.
          self.match_stack.pop();
          self.substitutions.remove(&expression);
        },

        MatchStack::ProducedMatchEquations(added) => {
          // Remove it.
          self.match_stack.pop();
          let new_length = self.equation_stack.len() - added as usize;
          self.equation_stack.truncate(new_length);
        },

      } // end match on top of the stack
    } // end loop
  }


  // Undoes the effects of the last call to `next()`, removes the match generator, and
  // restores any match equation corresponding to the match generator, if any.
  fn backtrack(&mut self) {
    let match_generator = self.undo();
    // Remove the match generator from the match stack.
    self.match_stack.pop();
    // Restore the match equation corresponding to the match generator.
    self.equation_stack.push(match_generator.match_equation());

  }


  /// If the variable is already bound, returns the value. Otherwise returns `None`.
  fn is_bound(&self, expression: RcExpression) -> Option<&RcExpression> {
    self.substitutions.get(&expression)
  }

}


impl Iterator for Matcher {
    type Item = SolutionSet;

    fn next(&mut self) -> Option<Self::Item> {
      if self.equation_stack.is_empty() {
        return None;
      }

      // loop {
        let me: MatchEquation = self.equation_stack.last().unwrap().clone();

        // Common Rules
        if let Some(rule) = RuleT::try_rule(&me) {
          self.push_rule(Rc::new(rule));

        } else if let Some(rule) = RuleIVE::try_rule(&me) {
          self.push_rule(Rc::new(rule));

        } else if let Some(rule) = RuleFVE::try_rule(&me) {
          self.push_rule(Rc::new(rule));
        }

        //// Break ////

        // A prerequisite for creating a `DestructuredFunctionEquation` and good
        // place to bail early.
        if me.pattern.kind()!=ExpressionKind::Function
            || me.ground.kind()!=ExpressionKind::Function
        {
          return None;
        }

        let dfe = DestructuredFunctionEquation::new(me);

        // Another opportunity to bail early.
        if dfe.pattern_function.head != dfe.ground_function.head {
          return None;
        }

        match (dfe.ground_function.commutative(), dfe.ground_function.associative()) {

          // Rules for Free Functons (neither associative nor commutative)
          (false, false) => {
            // Dec-F
            if let Some(rule) = RuleDecF::try_rule(&dfe){
              self.push_rule(Rc::new(rule));
            }
            // SVE-F
            else if let Some(rule) = RuleSVEF::try_rule(&dfe){
              self.push_rule(Rc::new(rule));
            }
          }

          // Rules for commutative functions
          (true, false) => {

            // Dec-C
            if let Some(rule) = RuleDecC::try_rule(&dfe) {
              self.push_rule(Rc::new(rule));
            }
            // SVE-C
            else if let Some(rule) = RuleSVEC::try_rule(&dfe) {
              self.push_rule(Rc::new(rule));
            }

          },

          // Rules for associative functions
          (false, true) => {

            // call try_rule for each associative rule.

          },



          (true, true) => todo!(),
        }



      None
    }
}
