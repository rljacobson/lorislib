/*!

A `Matcher` holds the state of the matching algorithm as it walks the
expression tree looking for a match. Most importantly, it keeps track of the
substitutions that are currently active.

In terms of Dundua, `Matcher` keeps track of $S$ and $\Gamma$. The set $S$ is the
set of active `MatchGenerator`s. Since future rule applications depend on a
`MatchGenerator`'s choice of how to transform the equation, the set `S` is
implemented as a stack. When a `MatchGenerator` is exhausted, it is popped from
the stack, and the next `MatchGenerator` is queried for the next substitution.

ToDo: Other state includes whether or not patterns are being held. A subexpression can
      be wrapped in `HoldPattern`. Inside of `HoldPattern`, pattern symbols are treated
      as literal symbols, not as patterns. Also, `Longest` and `Shortest` affect the order in
      which sequence variables generate matches. None of this is implemented.

*/



use std::{
  collections::HashMap,
  fmt::Display,
};

use crate::{
  logging::{
    Channel,
    log
  },
  context::Context,
};
use crate::atom::{
  Atom,
  AtomKind
};
use crate::attributes::Attributes;
use crate::format::{DisplayForm, Formattable};

use super::{
  associative::{
    RuleDecA,
    RuleFVEA,
    RuleIVEA,
    RuleSVEA
  },
  associative_commutative::{
    RuleDecAC,
    RuleFVEAC,
    RuleSVEAC,
    RuleIVEAC
  },
  common::{
    RuleFVE,
    RuleIVE,
    RuleT
  },
  commutative::{
    RuleDecC,
    RuleSVEC
  },
  free_functions::{
    RuleDecF,
    RuleSVEF
  },
  match_generator::{
    MatchGenerator,
    NextMatchResult,
    NextMatchResultList
  },
  MatchEquation,
  SolutionSet
};

pub type BoxedMatchGenerator = Box<dyn MatchGenerator<Item=NextMatchResultList>>;

/// Items that can be pushed onto the match stack.
pub(crate) enum MatchStack {

  /// The match generator responsible for the operations sitting immediately above it on
  /// the stack. Those operations are undone in order to get back to the
  /// match generator to call `next()`.
  MatchGenerator(BoxedMatchGenerator),

  /// A variable or sequence variable substitution. We only need to record the key
  /// (the expression) of the `SolutionSet` hashmap.
  Substitution(Atom),

  /// An operation representing pushing matching equations onto the equation stack.
  ProducedMatchEquations(u32),

}


impl MatchStack {

  /// Wraps the given `MatchGenerator`.
  pub fn rule(generator: BoxedMatchGenerator) -> MatchStack {
    MatchStack::MatchGenerator(generator)
  }

}


/// Holds the state of the in-process pattern matching attempt.
pub struct Matcher<'c> {
  /// The match_stack is where operations that change the state are recorded.
  /// Operations are pushed when they are done and popped when they are undone.
  match_stack: Vec<MatchStack>,
  /// The match equations that still need to be solved.
  equation_stack: Vec<MatchEquation>,
  /// The symbol table recording all variable/sequence variable bindings.
  substitutions: SolutionSet,
  /// The matcher needs to be able to look up the attributes of functions from the context.
  context: &'c Context
}


impl<'c> Display for Matcher<'c> {
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
    write!(f, "Γ={{{}}}\nS={{{}}}", equations, substitutions)
  }
}


impl<'c> Matcher<'c> {

  /// Create a new `MatchGenerator` for the match equation `pattern`≪`subject`.
  pub fn new(pattern: Atom, subject: Atom, context: &'c Context) -> Matcher {
    Matcher {
      match_stack: Vec::new(),
      equation_stack: vec![MatchEquation{pattern, ground: subject}],
      substitutions: HashMap::new(),
      context
    }
  }


  /// Pushes the given `MatchGenerator`.
  fn push_rule(&mut self, generator: BoxedMatchGenerator) {
    self.match_stack.push(MatchStack::MatchGenerator(generator));
  }


  /// Undoes the effects of the last call to `next()` and, for convenience, returns
  /// the responsible match generator in the form of an `Box<dyn MatchGenerator>` object.
  /// Upon return the `MatchGenerator` will be active, i.e. on top of the match
  /// stack.
  fn undo(&mut self) -> BoxedMatchGenerator {
    loop {
      match self.match_stack.pop().unwrap() {

        MatchStack::MatchGenerator(match_generator) => {
          // Leave the match generator on top of the match stack, and don't restore
          // its match equation.
          return match_generator;
        },

        MatchStack::Substitution(expression) => {
          // Remove it.
          self.substitutions.remove(&expression);
        },

        MatchStack::ProducedMatchEquations(added) => {
          // Remove it.
          log(Channel::Debug, 5, format!("Removing {} added equations from equation stack with len {}.", added, self.equation_stack.len()).as_str());
          let new_length = self.equation_stack.len() - added as usize;
          self.equation_stack.truncate(new_length);
        },

      } // end match on top of the stack
    } // end loop
  }


  /// Step 4.
  /// Undoes the effects of the last call to `next()`, removes the match generator, and
  /// restores any match equation corresponding to the match generator, if any.
  fn backtrack(&mut self) {
    log(Channel::Debug, 5, "Failed to match with that generator. Backtracking.".to_string().as_str());
    // Remove the match generator from the match stack.
    let match_generator = self.undo();
    // Restore the match equation corresponding to the match generator.
    self.equation_stack.push(match_generator.match_equation());

  }


  /// If the variable is already bound, returns the value. Otherwise returns `None`.
  fn is_bound(&self, expression: Atom) -> Option<&Atom> {
    self.substitutions.get(&expression)
  }

  /// Check which rule applies to the active match equation, creates the match
  /// generator for that rule, and pushes the match generator onto the match
  /// stack.
  fn select_rule(&mut self) -> Result<(), ()>{
    /*

      "The form and the conditions of the rules guarantee that no two rules apply to the same
      equation except if one of them is Dec-A or Dec-AC. Dec-A can apply to the equation that is
      transformed by FVE-A or IVE-A. Similarly, Dec-AC is an alternative of FVE-AC or IVE-AC."

      This modification was added to Dundua's paper on 4 March 2022 after I pointed out that not
      all solutions are produced if only one rule is applied.

      The rules Dec-A* always apply whenever FVE-A* or IVE-A* apply. Also, Dec-A* applies when
      the first argument of the pattern function is a non-function non-variable, i.e. a literal
      or symbol. Thus, we modify the definitions of FVE-A* or IVE-A* to have an encapsulated copy
      of Dec-A*. We also place Dec-A* _after_ FVE-A* or IVE-A* in the `if`-list of rules.

    */

    if self.equation_stack.is_empty() {
      // Nothing to select.
      return Err(());
    }

    let me: MatchEquation = self.equation_stack.pop().unwrap();
    // todo: Substitute bound variables with their values.

    log(Channel::Debug, 5, format!("Selecting rule. Match equation on stack: {}", me).as_str());
    // Common Rules
    if let Some(rule) = RuleT::try_rule(&me) {
      log(Channel::Debug, 5, format!("Creating Trivial rule for {}", me).as_str());
      self.push_rule(Box::new(rule));
      return Ok(());

    } else if let Some(rule) = RuleIVE::try_rule(&me) {
      log(Channel::Debug, 5, format!("Creating IVE for {}", me).as_str());
      self.push_rule(Box::new(rule));
      return Ok(());

    } else if let Some(rule) = RuleFVE::try_rule(&me) {
      log(Channel::Debug, 5, format!("Creating FVE for {}", me).as_str());
      self.push_rule(Box::new(rule));
      return Ok(());
    }

    // A prerequisite for destructuring f/g and good place to bail early.
    if me.pattern.kind() != AtomKind::SExpression
        || me.ground.kind() != AtomKind::SExpression
    {
      // Return match equation.
      self.equation_stack.push(me);
      return Err(());
    }

    // Another opportunity to bail early. This indicates program state that should be impossible.
    if me.pattern.head() != me.ground.head() {
      log(Channel::Debug, 5, "Both sides not functions.".to_string().as_str());
      // Return match equation.
      self.equation_stack.push(me);
      return Err(());
    }

    let ground_attributes: Attributes = self.context.get_attributes(me.ground.name().unwrap());

    match (ground_attributes.commutative(), ground_attributes.associative()) {

      // Rules for Free Functions (neither associative nor commutative)
      (false, false) => {
        // Dec-F
        if let Some(rule) = RuleDecF::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating Dec-F for {}", me).as_str());
          self.push_rule(Box::new(rule));
        }
        // SVE-F
        else if let Some(rule) = RuleSVEF::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating DVE-F for {}", me).as_str());
          self.push_rule(Box::new(rule));
        } else {
          // Return match equation.
          self.equation_stack.push(me);
          log(Channel::Debug, 5, format!("No applicable (free) rule found.").as_str());
          return Err(());
        }
        Ok(())
      }

      // Rules for commutative functions
      (true, false) => {

        // Dec-C
        if let Some(rule) = RuleDecC::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating Dec-C for {}", me).as_str());
          self.push_rule(Box::new(rule));
        }
        // SVE-C
        else if let Some(rule) = RuleSVEC::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating SVE-C for {}", me).as_str());
          self.push_rule(Box::new(rule));
        } else {
          // Return match equation.
          self.equation_stack.push(me);
          log(Channel::Debug, 5, format!("No applicable (commutative) rule found.").as_str());
          return Err(());
        }
        Ok(())
      },

      // Rules for associative functions
      (false, true) => {

        // SVE-A
        if let Some(rule) = RuleSVEA::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating SVE-A for {}", me).as_str());
          self.push_rule(Box::new(rule));
        }
        // FVE-A
        else if let Some(rule) = RuleFVEA::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating FVE-A for {}", me).as_str());
          self.push_rule(Box::new(rule));
        }
        // IVE-A
        else if let Some(rule) = RuleIVEA::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating IVE-A for {}", me).as_str());
          self.push_rule(Box::new(rule));
        }
        // Dec-A
        else if let Some(rule) = RuleDecA::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating Dec-A for {}", me).as_str());
          self.push_rule(Box::new(rule));
        } else {
          log(Channel::Debug, 5, format!("No applicable (associative) rule found.").as_str());
          // Return match equation.
          self.equation_stack.push(me);
          return Err(());
        }
        Ok(())
      },

      // Rules for associative-commutative symbols.
      (true, true) => {

        // SVE-AC
        if let Some(rule) = RuleSVEAC::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating SVE-AC for {}", me).as_str());
          self.push_rule(Box::new(rule));
        }
        // FVE-AC
        else if let Some(rule) = RuleFVEAC::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating FVE-AC for {}", me).as_str());
          self.push_rule(Box::new(rule));
        }
        // IVE-AC
        else if let Some(rule) = RuleIVEAC::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating IVE-AC for {}", me).as_str());
          self.push_rule(Box::new(rule));
        }
        // Dec-AC
        else if let Some(rule) = RuleDecAC::try_rule(&me) {
          log(Channel::Debug, 5, format!("Creating Dec-AC for {}", me).as_str());
          self.push_rule(Box::new(rule));
        } else {
          log(Channel::Debug, 5, format!("No applicable (associative-commutative) rule found.").as_str());
          // Return match equation.
          self.equation_stack.push(me);
          return Err(());
        }
        Ok(())
      }
    } // end match on (commutative, associative)

  } // end fetch_rule


  /// Step 2: Store the results of `next()` on the relevant stacks.
  fn process_next_match_list(&mut self, mut results: NextMatchResultList) {
  let mut equation_count: u32 = 0;

  for result in results.drain(..){
    match result {

      NextMatchResult::Substitution(substitution) => {
        self.substitutions.insert(substitution.variable.clone(), substitution.ground.clone());
        self.match_stack.push(MatchStack::Substitution(substitution.variable.clone()));
      }

      NextMatchResult::MatchEquation(match_equation) => {
        log(Channel::Debug, 5, format!("Pushing match equation: {}", match_equation).as_str());
        self.equation_stack.push(match_equation);
        equation_count += 1;
      }

    }
  }

  if equation_count > 0 {
    self.match_stack.push(MatchStack::ProducedMatchEquations(equation_count));
  }
}

}


impl<'c> Iterator for Matcher<'c> {
  type Item = SolutionSet;

  fn next(&mut self) -> Option<Self::Item> {
    // If the last match was successful, the equation stack will be empty. But
    // there could be more solutions possible, in which case backtracking
    // will put equations back on the stack.
    if self.equation_stack.is_empty() && self.match_stack.is_empty() {
      log(Channel::Debug, 5, "Both equation stack and match stack are empty. Done.".to_string().as_str());
      return None;
    }

    'step1: loop {


      // Step 1: Act on the active equation.
      if self.select_rule().is_err() {
        // Step 1.a If no rule applies…
        if self.match_stack.is_empty() {
          // Step 1.a.i. If the match stack is empty, halt with failure.
          return None;
        } else {
          // Step 1.a.ii. If there is an active match generator on top of the
          // matcher stack, undo the actions of the last match generated
          // from this match generator…
          log(Channel::Debug, 5, "Undoing the last match generator actions.");
          let match_generator: BoxedMatchGenerator = self.undo();
          // …but retain the active match generator.
          self.match_stack.push(MatchStack::MatchGenerator(match_generator));
          // Proceed to step 2.
        }
      } else {
        // Step 1.b If a rule applies, create the MatchGenerator for the rule,
        // (provide it the equation), and push it into the match stack. It
        // is now the active MatchGenerator.

        // This step happens in `self.select_rule()`
      }

      'step2: loop {
        // Step 2. Request a new match.
        match self.match_stack.last_mut() {

          None => {
            // Step 2.a
            log(Channel::Debug, 5, "Nothing on Match Stack.".to_string().as_str());
            return None
          }

          Some(MatchStack::MatchGenerator(match_generator)) => {
            // Step 2.b
            match match_generator.next() {

              Some(results) => {
                log(Channel::Debug, 5, "Match generator returned Some".to_string().as_str());
                self.process_next_match_list(results);
                // Step 3.b
                if self.equation_stack.is_empty(){
                  log(Channel::Debug, 4, "SUCCESS!".to_string().as_str());
                  return Some(self.substitutions.clone());
                }
                // Step 3.c
                continue 'step1;
              }

              None => {
                // Step 4.
                log(Channel::Debug, 5, "Match generator returned None. Trying to match again.".to_string().as_str());
                self.backtrack(); // Back to previous matcher.
                // Undo the match of the matcher that created the one we just popped.
                if self.match_stack.is_empty() {
                  return None;
                } else {
                  let match_generator = self.undo();
                  self.match_stack.push(MatchStack::MatchGenerator(match_generator));
                }
                continue 'step2;
              }

            }
          },

          Some(MatchStack::ProducedMatchEquations(me)) => {
            log(Channel::Debug, 5, format!("Bad state in Step 2. Expected a match generator, found # produced match equations: {}", me).as_str());
          },

          Some(MatchStack::Substitution(sub)) => {
            log(Channel::Debug, 5, format!("Bad state in Step 2. Expected a match generator, found substitution: {}", sub).as_str());
          }

        } // end match on self.match_stack.last_mut()

        continue 'step1
      } // end step 2 loop
    }

    // None
  }
}

pub fn display_solutions(solution_set: &SolutionSet) -> String {
  if solution_set.is_empty() {
    // println!("Substitution Set: {{EMPTY}}");
    String::from("EMPTY")
  } else {
    let mut subs = solution_set.iter()
        .map(|(k, v)|
            format!(
              "{} = {}",
              k.format(&DisplayForm::Matcher.into()),
              v.format(&DisplayForm::Matcher.into()),
            )
        )
        .collect::<Vec<String>>();
    subs.sort();
    format!("[ {} ]", subs.join(", "))
  }
}

// tests
// See mod.rs for the tests.
