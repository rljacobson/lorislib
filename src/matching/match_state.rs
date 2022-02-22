/*!

A `MatchState` holds the state of the matching algorithm as it walks the
expression tree looking for a match. Most importantly, it keeps track of the
substitutions that are currently active.

In terms of Dundua, `MatchState` keeps track of $S$ and $\Gamma$. The set $S$ is
the set of active `Matcher`s. Since future rule applications depend on a `Matcher`'s
choice of how to transform the equation, the set `S` is implemented as a stack.
When a `Matcher` is exhausted, it is popped from the stack, and the next `Matcher` is
queried for the next substitution.

Other state includes whether or not patterns are being held. A subexpression can
be wrapped in `HoldPattern`. Inside of `HoldPattern`, pattern symbols are treated
as literal symbols, not as patterns.

*/

use std::{collections::HashMap, fmt::Display, rc::Rc};

use crate::{expression::RcExpression};

use super::{matcher::Matcher, SolutionSet, MatchEquation};



/// Items that can be pushed onto the match stack.
#[derive(Clone)]
enum MatchStack {

  /// The matcher responsible for the operations sitting immediately above it on
  /// the stack. Those operations are undone in order to get back to the
  /// matcher to call `next()`.
  Matcher(Rc<dyn Matcher>),

  /// A variable or sequence variable substitution. We only need to record the key
  /// (the expression) of the `SolutionSet` hashmap.
  Substitution(RcExpression),

  /// An operation representing pushing matching equations onto the equation stack.
  ProducedMatchEquations(u32),

}

/// Holds the state of the in-process pattern matching attempt.
pub struct MatchState {
  /// The match_stack is where operations that change the state are recorded.
  /// Operations are pushed when they are done and popped when they are undone.
  match_stack: Vec<MatchStack>,
  /// The match equations that still need to be solved.
  equation_stack: Vec<MatchEquation>,
  /// The symbol table recording all veriable/sequence variable bindings.
  substitutions: SolutionSet,
}


impl Display for MatchState {
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


impl MatchState {

  /// Create a new `MatchState` for the match equation `pattern`≪`subject`.
  pub fn new(pattern: RcExpression, subject: RcExpression) -> MatchState {
    MatchState {
      match_stack: Vec::new(),
      equation_stack: vec![MatchEquation{pattern, ground: subject}],
      substitutions: HashMap::new(),
    }
  }


  /// Under the effects of the last call to `next()` and, for convenience, returns
  /// the responsible matcher in the form of an `Rc<Matcher>` object.
  /// Upon return the `Matcher` will be active, i.e. on top of the match
  /// stack.
  fn undo(&mut self) -> Rc<dyn Matcher> {
    loop {
      match self.match_stack.last().unwrap().clone() {

        MatchStack::Matcher(matcher) => {
          // Leave the matcher on top of the match stack.
          return matcher.clone();
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


  // Undoes the effects of the last call to `next()`, removes the matcher, and
  // restores any match equation corresponding to the matcher, if any.
  fn backtrack(&mut self) {
    let matcher = self.undo();
    // Remove the matcher from the match stack.
    self.match_stack.pop();
    // Restore the match equation corresponding to the matcher.
    self.equation_stack.push(matcher.match_equation());

  }


  /// If the variable is already bound, returns the value. Otherwise returns `None`.
  fn is_bound(&self, expression: RcExpression) -> Option<&RcExpression> {
    self.substitutions.get(&expression)
  }


}


impl Iterator for MatchState {
    type Item = SolutionSet;

    fn next(&mut self) -> Option<Self::Item> {



      None
    }
}
