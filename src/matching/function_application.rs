/*!

  Generators for associative function application,
    {x̅≈(t₁,…,tₙ)[ƒ]},
  and AC-function application,
    {x̅≈❴t₁,…,tₙ❵[ƒ]}.
  Commutative-only function application is not factored out into its own type. (See `RuleSVEC`.)

  # The Algorithm for Generating Σ{x̅≈(t₁,…,tₙ)[ƒ]}

  Singletons are a special case, because they can appear as either `t` or `ƒ(t)`.
  We track whether tₙ has ƒ applied according to whether the nth bit of
  self.applications is set. Enumerating all possibilities is as easy as
  counting from 0 to 2^m-1 where m is the number of singleton terms.

  As for the other groupings of terms via function application, we use the method
  of stars and bars.

  Example: How many ways are there to partition the ordered list 1 2 3?
  * * *
  *|* *
  * *|*
  *|*|*

  The key is to observe that the partition boundaries lie between the terms, and
  so there are n-1 partition boundaries (not counting the implicit ones on the
  extreme ends, not draw above.) Either a partition exists in a space or it
  does not. So there are 2^(n-1) partitions. We track whether there is a
  partition in space n according to whether the nth bit of `self.applications`
  is _not_ set. We use the logical not of the nth bit so that functions with
  fewer terms come first.


  # The Algorithm for Generating Σ{x̅≈❴t₁,…,tₙ❵[ƒ]}

  CORRECT: For each permutation of (t₁,…,tₙ), generate Σ{x̅≈(t₁,…,tₙ)[ƒ]} for the
  permutation.

  WRONG: I think it's enough to use Σ{x̅≈(t₁,…,tₙ)[ƒ]} and just permute the "top
  level" terms, that is, generate all permutations of the result sequences.

*/

use std::{
  marker::PhantomData,
  rc::Rc
};

use smallvec::smallvec;

use permutation_generator::PermutationGenerator32 as Permutations;

use crate::{
  expression::ExpressionKind,
  atoms::{
    Function,
    Sequence
  }, logging::log_at_level
};

use super::{
  match_generator::{
    NextMatchResult,
    MaybeNextMatchResult,
    MatchGenerator,
    NextMatchResultList
  },
  MatchEquation,
  destructure::DestructuredFunctionEquation
};


/// Marker trait indicating that every possible function application pattern is to
/// be enumerated. This can be an extremely large number for anything more than a
/// handful of terms.
pub struct EnumerateAll;
/// Onely gives the original sequence back.
pub struct EnumerateOne;
/// Enumerates every pattern in which every term is an argument to the function.
pub struct EnumerateNoUnapplied;


pub trait FunctionApplicationGenerator: Iterator<Item=Sequence>{
  fn new(function: Function) -> Self;
}

/// Associative Function Application Generator. We can match up to 33
/// arguments, which is already borderline computationally infeasible with this
/// implementation on present-day hardware.
pub struct AFAGenerator<EnumerationType> {
  function       : Function,
  /// A bit vector encoding which terms are outside of any function application;
  /// `singleton_state` is also recycled as a flag indicating exhaustion.
  singleton_state: u32,
  /// A bit vector encoding how terms are grouped into function applications.
  application_state   : u32,
  phantom        : PhantomData<EnumerationType>
}



impl<T> FunctionApplicationGenerator for AFAGenerator<T>
    where AFAGenerator<T>: Iterator<Item=Sequence>
{
  fn new(function: Function) -> AFAGenerator<T> {
    AFAGenerator::<T>{
      function,
      singleton_state  : 0,
      application_state: 0,
      phantom          : PhantomData:: default()
    }
  }
}

impl Iterator for AFAGenerator<EnumerateAll> {
  type Item = Sequence;

  fn next(&mut self) -> Option<Sequence> {
    let mut n = self.function.len();
    n = if n > 32 {
      32
    } else if n==0 {
      return None;
    } else {
       n
    };
    // The (n-1) in the formula below is because there are (n-1) spaces between n
    // elements.
    let max_application_state: u32 = ((1 << (n-1)) - 1) as u32;
    log_at_level(5, format!("application state: {}, n: {}, max_application_state: {}", self.application_state, n, max_application_state).as_str());

    if self.singleton_state == u32::MAX {
      return None;
    }

    // The "outer loop" iterates over `applications`, which defines the shape of
    // the result. The "inner loop" generates all ways of having a
    // singleton by itself or with the function applied. Iteration values
    // are updated at the bottom of the loop.

    // The "effective" application state. We do this so that the cases with f
    // unapplied come first. This seems less confusing than swapping the
    // meaning of a set bit.
    let application_state   = !(self.application_state as usize);
    let mut result_sequence = Sequence::default();
    // Position 0 is the implicit boundary on the far left of the sequence.
    // Position n is the boundary on the far right.
    let mut last_boundary_position = 0;
    let mut singleton_count        = 0;
    for position in 1..n+1 {
      if position == n || ((1 << (position-1)) & application_state) > 0 {
        // Boundary.

        // If last boundary position isn't the previous position checked, then
        // we just completed a run of a single function application.
        if position - last_boundary_position > 1 {

          let mut new_function = self.function.duplicate_head();
          for child_idx in last_boundary_position..position {
            new_function.children.push(self.function.part(child_idx));
          }

          result_sequence.push(Rc::new(new_function.into()));
        }
        // If last boundary position is the last position checked, then we have a singleton.
        else {
          if (1 << singleton_count) & self.singleton_state > 0 {
            log_at_level(5, format!("Singleton state is high. Wrapping in function. STATE: {}, COUNT: {}", self.singleton_state, singleton_count).as_str());
            // Wrap it in a function.
            let mut new_function = self.function.duplicate_head();
            new_function.push(self.function.part(position-1));

            result_sequence.push(Rc::new(new_function.into()));
          } else {
            log_at_level(5, "Singleton state is low. Not wrapping in function.".to_string().as_str());
            result_sequence.push(self.function.part(position-1));
          }

          singleton_count += 1;
        }

        last_boundary_position = position;
      } // end if boundary
      else {
        // Not a boundary. We are currently iterating over a run that will be inside a function.
        // Nothing to do.
      }


    }

    // Update the state.
    // On the last result sequence, we set self.singleton_state to u32::MAX as a
    // flag to indicate exhaustion. We have to check for this condition so
    // we don't overflow self.singleton_state.
    if self.singleton_state != u32::MAX {
      log_at_level(5, "Increment singleton state.");
      self.singleton_state += 1;
    }
    if self.singleton_state == (1<<singleton_count) {
      // Past the maximum. Time to reset and yield control to the "outer loop".
      if self.application_state == max_application_state {
        // If we have reached the maximum application_state, we are returning the
        // last result. Next call will return None.
        // self.singleton_state is recycled as a flag indicating
        // exhaustion.
        log_at_level(5, "Setting singleton state to MAX, because application state is maximum.");
        self.singleton_state = u32::MAX;
      } else {
        // We haven't exhausted the generator yet.
        log_at_level(5, "Resetting singleton state.\nIncrementing application_state.");
        self.singleton_state = 0;
        // This is the only time we update the state of the outer loop.
        self.application_state += 1;
      }

    }

    Some(result_sequence)
  }


}


impl Iterator for AFAGenerator<EnumerateOne> {
  type Item = Sequence;

    fn next(&mut self) -> Option<Sequence> {
      // One shot.
      if self.singleton_state == u32::MAX {
        return None;
      }
      self.singleton_state = u32::MAX;

      Some(Sequence::from_children(self.function.children.clone()))
    }
}


impl Iterator for AFAGenerator<EnumerateNoUnapplied> {
  type Item = Sequence;

  fn next(&mut self) -> Option<Sequence> {
    // Very similar to EnumerateAll, except there is no `self.singleton_state`.
    let mut n = self.function.len();
    n = if n > 32 { 32 } else { n };
    // The (n-1) in the formula below is because there are (n-1) spaces between n
    // elements.
    let max_application_state: u32 = ((1 << (n-1)) - 1) as u32;

    if self.application_state == max_application_state {
      // self.singleton_state is recycled as a flag indicating exhaustion.
      if self.singleton_state == u32::MAX {
        return None;
      } else {
        self.singleton_state = u32::MAX;
      }
    }

    // The "loop" iterates over `applications`, which defines the shape of the result.
    // Values are updated at the bottom of the loop.

    // The "effective" application state.
    let application_state   = !(self.application_state as usize);
    let mut result_sequence = Sequence::default();
    // Position 0 is the implicit boundary on the far left of the sequence.
    // Position n is the boundary on the far right.
    let mut last_boundary_position = 0;
    for position in 1..n+1 {
      if position == n || ((1 << (position-1)) & application_state) > 0 {
        // Boundary.
        let mut new_function = self.function.duplicate_head();

        for child_idx in last_boundary_position..position {
          new_function.push(self.function.part(child_idx));
        }

        result_sequence.push(Rc::new(new_function.into()));

        last_boundary_position = position;
      } // end if boundary
      else {
        // Not a boundary. We are currently iterating over a run that will be inside a function.
        // Nothing to do.
      }


    }

    // Update the state.
    // Don't overflow if this is the last possible value of
    // `self.application_state`. Is this the last application state?
    if self.application_state != max_application_state {
      self.application_state += 1;
    }

    Some(result_sequence)
  }
}


/// Associative-Commutative Function Application Generator
pub struct AFACGenerator<EnumerationType> {
  function     : Function,
  afa_generator: AFAGenerator<EnumerationType>,
  permutations : Permutations
}


impl FunctionApplicationGenerator for AFACGenerator<EnumerateAll> {
  fn new(function: Function) -> AFACGenerator<EnumerateAll> {
    log_at_level(5, format!("Creating AF-AC for {}", function).as_str());

    let mut permutations = Permutations::new(function.len() as u8).unwrap();
    // The first permutation is the identity, so just clone the function.
    permutations.next();
    let afa_generator    = AFAGenerator::<EnumerateAll>::new(function.clone());

    AFACGenerator::<EnumerateAll>{
      function,
      afa_generator,
      permutations,
    }
  }
}

impl Iterator for AFACGenerator<EnumerateAll> {
  type Item = Sequence;

  fn next(&mut self) -> Option<Sequence> {

    match self.afa_generator.next() {

      None => {
        // Get the next afa_generator element.
        match self.permutations.next() {

          None => {
            // This generator is exhausted.
            None
          },

          Some(permutation) => {
            let ordered_children =
              permutation.map(|n| self.function.part(n as usize))
                         .collect::<Vec<_>>();
            let mut permuted_function = self.function.duplicate_head();
            permuted_function.children = ordered_children;
            self.afa_generator = AFAGenerator::<EnumerateAll>::new(permuted_function);

            self.afa_generator.next()
          }

        } // end match on self.permutations.next()
      } // end branch self.afa_generator.next()==None


      _some => {
        _some
      }

    } // end match on self.afa_generator.next()

  }
}

impl FunctionApplicationGenerator for AFACGenerator<EnumerateOne> {
  fn new(function: Function) -> AFACGenerator<EnumerateOne> {
    let permutations  = Permutations::new(1).unwrap();
    let afa_generator = AFAGenerator::<EnumerateOne>::new(function.clone());

    AFACGenerator::<EnumerateOne>{
      function,
      afa_generator,
      permutations,
    }
  }
}

impl Iterator for AFACGenerator<EnumerateOne> {
  type Item = Sequence;

  fn next(&mut self ) -> Option<Sequence> {
    self.afa_generator.next()
  }
}


impl FunctionApplicationGenerator for AFACGenerator<EnumerateNoUnapplied> {
  fn new(function: Function) -> AFACGenerator<EnumerateNoUnapplied> {
    let mut permutations = Permutations::new(function.len() as u8).unwrap();
    // The first permutation is the identity, so just clone the function.
    permutations.next();
    let afa_generator    = AFAGenerator::<EnumerateNoUnapplied>::new(function.clone());

    AFACGenerator::<EnumerateNoUnapplied>{
      function,
      afa_generator,
      permutations,
    }
  }
}


impl Iterator for AFACGenerator<EnumerateNoUnapplied> {
  type Item = Sequence;


  fn next(&mut self) -> Option<Sequence> {
    // let result: Option<Sequence> = ;


    match self.afa_generator.next() {

      None => {
        // Get the next afa_generator element.
        match self.permutations.next() {

          None => {
            // This generator is exhausted.
            None
          },

          Some(permutation) => {
            let ordered_children =
              permutation.map(|n| self.function.part(n as usize))
                         .collect::<Vec<_>>();
            let mut permuted_function = self.function.duplicate_head();
            permuted_function.children = ordered_children;
            self.afa_generator = AFAGenerator::<EnumerateNoUnapplied>::new(permuted_function);

            self.afa_generator.next()
          }

        } // end match on self.permutations.next()
      } // end branch self.afa_generator.next()==None


      _some => {
        _some
      }

    } // end match on self.afa_generator.next()

  }
}



pub struct RuleSVE<T>
  where T: FunctionApplicationGenerator {
  dfe: DestructuredFunctionEquation,
  /// A `Sequence`, holds the terms of the ground that we have attempted to match
  /// against so far.
  ground_sequence: Sequence,
  /// SVE-A iterates over both the subset of the children and S={x&#773;≈(t̃₁)[ƒ]}.
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
  // This is `None` if we have not yet produced the empty sequence.
  #[cfg(not(feature = "strict-associativity"))]
  afa_generator: Option<Box<T>>,
  #[cfg(feature = "strict-associativity")]
  afa_generator: Box<T>
}

impl<T> MatchGenerator for RuleSVE<T>
    where T: FunctionApplicationGenerator
{
  fn match_equation(&self) -> MatchEquation {
    self.dfe.match_equation.clone()
  }
}

impl<T> Iterator for RuleSVE<T>
    where T: FunctionApplicationGenerator
{
  type Item = NextMatchResultList;

  fn next(&mut self) -> MaybeNextMatchResult {
    // Have we produced the empty sequence?
    #[cfg(not(feature = "strict-associativity"))]
    match &mut self.afa_generator {
      None => {
        self.afa_generator = Some(Box::new(T::new(self.dfe.ground_function.duplicate_head())));
        // Return the empty sequence.
        self.make_next(Sequence::default())
      },

      Some(afa_generator) => {
        let ordered_sequence = // The result of this match
            match afa_generator.next() {
              None => {
                // Are there any more terms to take?
                if self.dfe.ground_function.len() == self.ground_sequence.len() {
                  // No more terms.
                  return None;
                }

                // Take the next term from the ground function.
                self.ground_sequence.children.push(
                  self.dfe.ground_function.children[
                      self.ground_sequence.len()
                      ].clone()
                );

                // Create a new AFAGenerator.
                let mut afa_function = self.dfe.ground_function.duplicate_head();
                afa_function.children = self.ground_sequence.children.clone();

                let mut new_afa_generator = T::new(afa_function);
                let next_result = new_afa_generator.next().unwrap();
                self.afa_generator = Some(Box::new(new_afa_generator));

                next_result
              }

              Some(next_result) => next_result
            }; // end match on self.afa_generator.next

        self.make_next(ordered_sequence)
      }
    }

    #[cfg(feature = "strict-associativity")]
    {
    let ordered_sequence = // The result of this match
    // Should
      match self.afa_generator.next() {
        None => {
          // Are there any more terms to take?
          if self.dfe.ground_function.len() == self.ground_sequence.len() {
            // No more terms.
            return None;
          }

          // Take the next term from the ground function.
          self.ground_sequence.children.push(
            self.dfe.ground_function.children[
                self.ground_sequence.len()
                ].clone()
          );

          // Create a new AFAGenerator.
          let mut afa_function = self.dfe.ground_function.duplicate_head();
          afa_function.children = self.ground_sequence.children.clone();

          let mut new_afa_generator = T::new(afa_function);
          let next_result = new_afa_generator.next().unwrap();


          self.afa_generator = Box::new(new_afa_generator);

          next_result
        }

        Some(next_result) => next_result
      }; // end match on self.afa_generator.next

      self.make_next(ordered_sequence)
    }
  }
}


impl<T> RuleSVE<T>
    where T: FunctionApplicationGenerator
{
  pub fn new(me: MatchEquation) -> RuleSVE<T> {
    let dfe = DestructuredFunctionEquation::new(&me).unwrap();

    #[cfg(feature = "strict-associativity")]
    let afa_generator = Box::new(T::new(dfe.ground_function.duplicate_head()));

    RuleSVE{
      dfe,
      ground_sequence: Sequence::default(),
      #[cfg(not(feature = "strict-associativity"))]
      afa_generator  : None,
      #[cfg(feature = "strict-associativity")]
      afa_generator,
    }
  } // end new RuleSVE<T

  // Constructs the next result using components of `self`.
  fn make_next(&self, ordered_sequence: Sequence) -> MaybeNextMatchResult {
    let mut match_equation_ground = self.dfe.ground_function.duplicate_head();
    // Todo: Does this do the right thing when `ground_function.len()==ground_sequence.len()`?
    self.dfe.ground_function
        .children[self.ground_sequence.len()..]
        .clone_into(
          &mut match_equation_ground.children
        );

    let result_equation =
      NextMatchResult::MatchEquation(
        MatchEquation{
          pattern: self.dfe.pattern_rest.clone(),
          ground: Rc::new(match_equation_ground.into())
        }
      );

    let result_substitution = NextMatchResult::sub(
      self.dfe.pattern_first.clone(),
      Rc::new(ordered_sequence.into())
    );

    Some(smallvec![result_equation, result_substitution])
  }


  pub fn try_rule(dfe: &DestructuredFunctionEquation) -> Option<Self> {
    // The only requirement is that pattern's first child is a sequence variable.
    if dfe.pattern_function.len() > 0
      && dfe.pattern_function.part(0).kind() == ExpressionKind::SequenceVariable {

      Some(
        Self{
          dfe            : dfe.clone(),
          ground_sequence: Sequence::default(),
          #[cfg(not(feature = "strict-associativity"))]
          afa_generator  : None,
          #[cfg(feature = "strict-associativity")]
          afa_generator  : Box::new(T::new(dfe.ground_function.duplicate_head())),
        }
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
  use crate::{atoms::{Function, Symbol}, expression::RcExpression};


  #[test]
  fn generate_all_afa_applications() {
    let children = vec!["a", "b", "c"].iter().map(|x| Rc::new(Symbol::from(*x).into())).collect::<Vec<RcExpression>>();
    let mut f = Function::with_symbolic_head("ƒ");
    f.children = children;

    let mut afa_generator = AFAGenerator::<EnumerateAll>::new(f);

    assert_eq!("(a, b, c)", afa_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, b, c)", afa_generator.next().unwrap().to_string());
    assert_eq!("(a, ƒ❨b❩, c)", afa_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨b❩, c)", afa_generator.next().unwrap().to_string());
    assert_eq!("(a, b, ƒ❨c❩)", afa_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, b, ƒ❨c❩)", afa_generator.next().unwrap().to_string());
    assert_eq!("(a, ƒ❨b❩, ƒ❨c❩)", afa_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨b❩, ƒ❨c❩)", afa_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a, b❩, c)", afa_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a, b❩, ƒ❨c❩)", afa_generator.next().unwrap().to_string());
    assert_eq!("(a, ƒ❨b, c❩)", afa_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨b, c❩)", afa_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨a, b, c❩", afa_generator.next().unwrap().to_string());
    assert_eq!(None, afa_generator.next());

    // for result in afa_generator {
    //   println!("{}", result);
    // }

  }


  #[test]
  fn generate_all_afac_applications() {
    let children = vec!["a", "b", "c"].iter().map(|x| Rc::new(Symbol::from(*x).into())).collect::<Vec<RcExpression>>();
    let mut f = Function::with_symbolic_head("ƒ");
    f.children = children;

    let mut afac_generator = AFACGenerator::<EnumerateAll>::new(f);

    // for result in afac_generator {
    //   println!("{}", result);
    // }

    assert_eq!("(a, b, c)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, b, c)", afac_generator.next().unwrap().to_string());
    assert_eq!("(a, ƒ❨b❩, c)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨b❩, c)", afac_generator.next().unwrap().to_string());
    assert_eq!("(a, b, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, b, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(a, ƒ❨b❩, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨b❩, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a, b❩, c)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a, b❩, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(a, ƒ❨b, c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨b, c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨a, b, c❩", afac_generator.next().unwrap().to_string());
    assert_eq!("(a, c, b)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, c, b)", afac_generator.next().unwrap().to_string());
    assert_eq!("(a, ƒ❨c❩, b)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨c❩, b)", afac_generator.next().unwrap().to_string());
    assert_eq!("(a, c, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, c, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(a, ƒ❨c❩, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨c❩, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a, c❩, b)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a, c❩, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(a, ƒ❨c, b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨c, b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨a, c, b❩", afac_generator.next().unwrap().to_string());
    assert_eq!("(b, a, c)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, a, c)", afac_generator.next().unwrap().to_string());
    assert_eq!("(b, ƒ❨a❩, c)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, ƒ❨a❩, c)", afac_generator.next().unwrap().to_string());
    assert_eq!("(b, a, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, a, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(b, ƒ❨a❩, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, ƒ❨a❩, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b, a❩, c)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b, a❩, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(b, ƒ❨a, c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, ƒ❨a, c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨b, a, c❩", afac_generator.next().unwrap().to_string());
    assert_eq!("(b, c, a)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, c, a)", afac_generator.next().unwrap().to_string());
    assert_eq!("(b, ƒ❨c❩, a)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, ƒ❨c❩, a)", afac_generator.next().unwrap().to_string());
    assert_eq!("(b, c, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, c, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(b, ƒ❨c❩, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, ƒ❨c❩, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b, c❩, a)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b, c❩, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(b, ƒ❨c, a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, ƒ❨c, a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨b, c, a❩", afac_generator.next().unwrap().to_string());
    assert_eq!("(c, a, b)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, a, b)", afac_generator.next().unwrap().to_string());
    assert_eq!("(c, ƒ❨a❩, b)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, ƒ❨a❩, b)", afac_generator.next().unwrap().to_string());
    assert_eq!("(c, a, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, a, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(c, ƒ❨a❩, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, ƒ❨a❩, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c, a❩, b)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c, a❩, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(c, ƒ❨a, b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, ƒ❨a, b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨c, a, b❩", afac_generator.next().unwrap().to_string());
    assert_eq!("(c, b, a)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, b, a)", afac_generator.next().unwrap().to_string());
    assert_eq!("(c, ƒ❨b❩, a)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, ƒ❨b❩, a)", afac_generator.next().unwrap().to_string());
    assert_eq!("(c, b, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, b, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(c, ƒ❨b❩, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, ƒ❨b❩, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c, b❩, a)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c, b❩, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(c, ƒ❨b, a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, ƒ❨b, a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨c, b, a❩", afac_generator.next().unwrap().to_string());
    assert_eq!(None, afac_generator.next());
  }


  #[test]
  fn generate_one_afa_application() {
    let children = vec!["a", "b", "c"].iter().map(|x| Rc::new(Symbol::from(*x).into())).collect::<Vec<RcExpression>>();
    let mut f = Function::with_symbolic_head("ƒ");
    f.children = children;

    let mut afa_generator = AFAGenerator::<EnumerateOne>::new(f);

    assert_eq!("(a, b, c)", afa_generator.next().unwrap().to_string());
    assert_eq!(None, afa_generator.next());

  }

  #[test]
  fn generate_one_afac_application() {
    let children = vec!["a", "b", "c"].iter().map(|x| Rc::new(Symbol::from(*x).into())).collect::<Vec<RcExpression>>();
    let mut f = Function::with_symbolic_head("ƒ");
    f.children = children;

    let mut afac_generator = AFACGenerator::<EnumerateOne>::new(f);

    assert_eq!("(a, b, c)", afac_generator.next().unwrap().to_string());
    assert_eq!(None, afac_generator.next());
  }


  #[test]
  fn generate_no_unapplied_afa_applications() {
    let children = vec!["a", "b", "c"].iter().map(|x| Rc::new(Symbol::from(*x).into())).collect::<Vec<RcExpression>>();
    let mut f = Function::with_symbolic_head("ƒ");
    f.children = children;

    let mut afa_generator = AFAGenerator::<EnumerateNoUnapplied>::new(f);

    assert_eq!("(ƒ❨a❩, ƒ❨b❩, ƒ❨c❩)", afa_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a, b❩, ƒ❨c❩)", afa_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨b, c❩)", afa_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨a, b, c❩", afa_generator.next().unwrap().to_string());
    assert_eq!(None, afa_generator.next());
  }



  #[test]
  fn generate_no_unapplied_afac_applications() {
    let children = vec!["a", "b", "c"].iter().map(|x| Rc::new(Symbol::from(*x).into())).collect::<Vec<RcExpression>>();
    let mut f = Function::with_symbolic_head("ƒ");
    f.children = children;

    let mut afac_generator = AFACGenerator::<EnumerateNoUnapplied>::new(f);

    // for res in afac_generator {
    //   println!("{}", res);
    // }
    assert_eq!("(ƒ❨a❩, ƒ❨b❩, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a, b❩, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨b, c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨a, b, c❩", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨c❩, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a, c❩, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨a❩, ƒ❨c, b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨a, c, b❩", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, ƒ❨a❩, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b, a❩, ƒ❨c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, ƒ❨a, c❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨b, a, c❩", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, ƒ❨c❩, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b, c❩, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨b❩, ƒ❨c, a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨b, c, a❩", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, ƒ❨a❩, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c, a❩, ƒ❨b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, ƒ❨a, b❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨c, a, b❩", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, ƒ❨b❩, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c, b❩, ƒ❨a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("(ƒ❨c❩, ƒ❨b, a❩)", afac_generator.next().unwrap().to_string());
    assert_eq!("ƒ❨c, b, a❩", afac_generator.next().unwrap().to_string());
    assert_eq!(None, afac_generator.next());
  }

}
