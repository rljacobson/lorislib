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
```text
  * * *
  *|* *
  * *|*
  *|*|*
```

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
  cmp::min,
  rc::Rc
};

use smallvec::smallvec;

use permutation_generator::PermutationGenerator32 as Permutations;

use crate::{
  atom::{
    Atom,
    SExpression,
  },
  logging::{
    Channel,
    log
  }
};


use super::{
  match_generator::{
    NextMatchResult,
    MaybeNextMatchResult,
    MatchGenerator,
    NextMatchResultList
  },
  MatchEquation,
};


/// Marker trait indicating that every possible function application pattern is to
/// be enumerated. This can be an extremely large number for anything more than a
/// handful of terms.
pub struct EnumerateAll;
/// Only gives the original sequence back.
pub struct EnumerateOne;
/// Enumerates every pattern in which every term is an argument to the function.
pub struct EnumerateNoUnapplied;

type Sequence = Vec<Atom>;

pub trait FunctionApplicationGenerator: Iterator<Item=Sequence>{
  fn new(function: Atom) -> Self;
}

/// Associative Function Application Generator. We can match up to 33
/// arguments, which is already borderline computationally infeasible with this
/// implementation on present-day hardware.
pub struct AFAGenerator<EnumerationType> {
  function         : Atom,
  /// A bit vector encoding which terms are outside of any function application;
  /// `singleton_state` is also recycled as a flag indicating exhaustion.
  singleton_state  : u32,
  /// A bit vector encoding how terms are grouped into function applications.
  application_state: u32,
  phantom          : PhantomData<EnumerationType>
}



impl<T> FunctionApplicationGenerator for AFAGenerator<T>
    where AFAGenerator<T>: Iterator<Item=Sequence>
{
  fn new(function: Atom) -> AFAGenerator<T> {
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
    let n = min(self.function.len(), 32);
    if n==0 {
      return None;
    }
    // The (n-1) in the formula below is because there are (n-1) spaces between n
    // elements.
    let max_application_state: u32 = ((1 << (n-1)) - 1) as u32;
    log(
      Channel::Debug,
      5,
      format!(
        "application state: {}, n: {}, max_application_state: {}",
        self.application_state,
        n,
        max_application_state
      ).as_str()
    );

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
          let function_children = SExpression::children(&self.function);
          let mut new_function_children = vec![function_children[0].clone()];
          new_function_children.extend(
            (last_boundary_position..position).map(|child_idx| {function_children[child_idx+1].clone()})
          );
          let new_function = Atom::SExpression(Rc::new(new_function_children));

          result_sequence.push(new_function);
        }
        // If last boundary position is the last position checked, then we have a singleton.
        else {
          if (1 << singleton_count) & self.singleton_state > 0 {
            log(
              Channel::Debug,
              5,
              format!(
                "Singleton state is high. Wrapping in function. STATE: {}, COUNT: {}",
                self.singleton_state,
                singleton_count).as_str()
            );
            // Wrap it in a function.
            let new_function = Atom::SExpression(Rc::new(
              vec![self.function.head(), SExpression::part(&self.function, position)]
            ));
            result_sequence.push(new_function);

          } else {
            log(Channel::Debug, 5, "Singleton state is low. Not wrapping in function.".to_string().as_str());
            result_sequence.push(SExpression::part(&self.function, position));
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
      log(Channel::Debug, 5, "Increment singleton state.");
      self.singleton_state += 1;
    }
    if self.singleton_state == (1<<singleton_count) {
      // Past the maximum. Time to reset and yield control to the "outer loop".
      if self.application_state == max_application_state {
        // If we have reached the maximum application_state, we are returning the
        // last result. Next call will return None.
        // self.singleton_state is recycled as a flag indicating
        // exhaustion.
        log(
          Channel::Debug,
          5,
          "Setting singleton state to MAX, because application state is maximum."
        );
        self.singleton_state = u32::MAX;
      } else {
        // We haven't exhausted the generator yet.
        log(Channel::Debug, 5, "Resetting singleton state. Incrementing application_state.");
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

      Some(
        SExpression::children(&self.function)[1..].to_vec()
      )
    }
}


impl Iterator for AFAGenerator<EnumerateNoUnapplied> {
  type Item = Sequence;

  fn next(&mut self) -> Option<Sequence> {
    // Very similar to EnumerateAll, except there is no `self.singleton_state`.
    let n = min(self.function.len(), 32);
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
        let function_children = SExpression::children(&self.function);
        let mut new_function_children = vec![function_children[0].clone()];
        new_function_children.extend(
          (last_boundary_position..position).map(|child_idx| {function_children[child_idx+1].clone()})
        );
        let new_function = Atom::SExpression(Rc::new(new_function_children));

        result_sequence.push(new_function);

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
  function     : Atom,
  afa_generator: AFAGenerator<EnumerationType>,
  permutations : Permutations
}


impl FunctionApplicationGenerator for AFACGenerator<EnumerateAll> {
  fn new(function: Atom) -> AFACGenerator<EnumerateAll> {
    log(Channel::Debug, 5, format!("Creating AF-AC for {}", function).as_str());

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
            let ordered_children: Vec<Atom> =
              permutation.map(|n| SExpression::part(&self.function, n as usize + 1))
                         .collect::<Vec<_>>();
            let permuted_function: Atom = SExpression::new(self.function.head(), ordered_children);
            self.afa_generator = AFAGenerator::<EnumerateAll>::new(permuted_function);

            self.afa_generator.next()
          }

        } // end match on self.permutations.next()
      } // end branch self.afa_generator.next()==None


      some => {
        some
      }

    } // end match on self.afa_generator.next()

  }
}

impl FunctionApplicationGenerator for AFACGenerator<EnumerateOne> {
  fn new(function: Atom) -> AFACGenerator<EnumerateOne> {
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
  fn new(function: Atom) -> AFACGenerator<EnumerateNoUnapplied> {
    let mut permutations = Permutations::new(function.len() as u8).unwrap(); // skip the head
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

// todo: Implement this in `AFACGenerator<EnumerationType>` (generically) if possible.
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
            let ordered_children: Vec<Atom> =
                permutation.map(|n| SExpression::part(&self.function, n as usize + 1))
                           .collect::<Vec<_>>();
            let permuted_function: Atom = SExpression::new(self.function.head(), ordered_children);
            self.afa_generator = AFAGenerator::<EnumerateNoUnapplied>::new(permuted_function);

            self.afa_generator.next()
          }

        } // end match on self.permutations.next()
      } // end branch self.afa_generator.next()==None


      some => {
        some
      }

    } // end match on self.afa_generator.next()

  }
}



pub struct RuleSVE<T>
  where T: FunctionApplicationGenerator {
  match_equation: MatchEquation,
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
    self.match_equation.clone()
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
        self.afa_generator = Some(Box::new(T::new(SExpression::duplicate_with_head(self.match_equation.ground))));
        // Return the empty sequence.
        self.make_next(Sequence::default())
      },

      Some(afa_generator) => {
        let ordered_sequence = // The result of this match
            match afa_generator.next() {
              None => {
                // Are there any more terms to take?
                if self.match_equation.ground.len() == self.ground_sequence.len() {
                  // No more terms.
                  return None;
                }

                // Take the next term from the ground function.
                self.ground_sequence.push(
                  SExpression::part(
                    self.match_equation.ground,
                    self.ground_sequence.len() + 1 // add 1 to skip head
                  )
                );

                // Create a new AFAGenerator.
                let mut afa_function = SExpression::new(self.match_equation.ground.head(), self.ground_sequence.clone());

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
      match self.afa_generator.next() {
        None => {
          // Are there any more terms to take?
          if self.match_equation.ground.len() == self.ground_sequence.len(){
            // No more terms.
            return None;
          }
          //
          // log(
          //   Channel::Debug,
          //   5,
          //   format!(
          //     "GROUND SEQUENCE: [{}]",
          //     self.ground_sequence.iter()
          //         .map(|a| a.format(&DisplayForm::Matcher.into()) )
          //         .collect::<Vec<String>>()
          //         .join(", ")
          //   ).as_str(),
          // );

          // Take the next term from the ground function.
          self.ground_sequence.push(
            SExpression::part(
              &self.match_equation.ground,
              self.ground_sequence.len()+1 // add 1 to skip head
            )
          );

          // Create a new AFAGenerator.
          let afa_function = SExpression::new(self.match_equation.ground.head(), self.ground_sequence.clone());

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

    #[cfg(feature = "strict-associativity")]
    let afa_generator = Box::new(T::new(SExpression::duplicate_with_head(&me.ground)));

    RuleSVE{
      match_equation: me,
      ground_sequence: Sequence::default(),
      #[cfg(not(feature = "strict-associativity"))]
      afa_generator  : None,
      #[cfg(feature = "strict-associativity")]
      afa_generator,
    }
  } // end new RuleSVE<T

  // Constructs the next result using components of `self`.
  fn make_next(&self, ordered_sequence: Sequence) -> MaybeNextMatchResult {

    let match_equation_ground = { // scope of extras
      let mut match_equation_ground_children = vec![self.match_equation.ground.head()];
      match_equation_ground_children.extend(
        // Todo: Does this do the right thing when `ground_function.len()==ground_sequence.len()`?
        SExpression::children(&self.match_equation.ground)[self.ground_sequence.len()+1..].iter().cloned()
      );
      Atom::SExpression(Rc::new(match_equation_ground_children))
    };

    let result_equation =
      NextMatchResult::MatchEquation(
        MatchEquation{
          pattern: self.match_equation.pattern_rest(),
          ground: match_equation_ground
        }
      );

    let result_substitution = NextMatchResult::sub(
      self.match_equation.pattern_first(),
      SExpression::sequence(ordered_sequence)
    );

    Some(smallvec![result_equation, result_substitution])
  }


  pub fn try_rule(me: &MatchEquation) -> Option<Self> {
    // log(
    //   Channel::Debug,
    //   5,
    //   format!(
    //     "TRYING RuleSVEAC. Pattern: {} Ground: {} pattern.len={} ground.len={}",
    //     me.pattern,
    //     me.ground,
    //     me.pattern.len(),
    //     me.ground.len(),
    //   ).as_str()
    // );

    // The only requirement is that pattern's first child is a sequence variable.
    if me.pattern.len() > 0
      && SExpression::part(&me.pattern, 1).is_sequence_variable().is_some() {

      Some(
        Self{
          match_equation : me.clone(),
          ground_sequence: Sequence::default(),
          #[cfg(not(feature = "strict-associativity"))]
          afa_generator  : None,
          #[cfg(feature = "strict-associativity")]
          afa_generator  : Box::new(T::new(SExpression::duplicate_with_head(&me.ground))),
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
  use crate::{
    atom::{
      Atom,
      Symbol,
    },
  };
  use crate::format::{DisplayForm, Formattable};

  // Only used for testing and debugging.
  fn sequence_to_string(seq: Sequence) -> String {
    if seq.len() == 1 {
      format!("{}",
              seq.first().unwrap().format(&DisplayForm::Matcher.into())
      )
    } else {
    format!(
      "({})",
      seq.iter().map(|a| a.format(&DisplayForm::Matcher.into())).collect::<Vec<String>>().join(", ")
      )
    }
  }


  #[test]
  fn generate_all_afa_applications() {
    let children = vec!["ƒ", "a", "b", "c"].iter().map(|x| Symbol::from_static_str(x)).collect::<Vec<Atom>>();
    let f = Atom::SExpression(Rc::new(children));

    let mut afa_generator = AFAGenerator::<EnumerateAll>::new(f);

    assert_eq!("(a, b, c)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, b, c)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(a, ƒ❨b❩, c)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨b❩, c)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(a, b, ƒ❨c❩)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, b, ƒ❨c❩)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(a, ƒ❨b❩, ƒ❨c❩)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨b❩, ƒ❨c❩)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(ƒ❨a, b❩, c)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(ƒ❨a, b❩, ƒ❨c❩)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(a, ƒ❨b, c❩)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨b, c❩)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("ƒ❨a, b, c❩", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!(None, afa_generator.next());

    // for result in afa_generator {
    //   println!("{}", result);
    // }

  }


  #[test]
  fn generate_all_afac_applications() {
    let children = vec!["ƒ", "a", "b", "c"].iter().map(|x| Symbol::from_static_str(x)).collect::<Vec<Atom>>();
    let f = Atom::SExpression(Rc::new(children));

    let mut afac_generator = AFACGenerator::<EnumerateAll>::new(f);

    // for result in afac_generator {
    //   println!("{}", result);
    // }
    assert_eq!("(a, b, c)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, b, c)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(a, ƒ❨b❩, c)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨b❩, c)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(a, b, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, b, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(a, ƒ❨b❩, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨b❩, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a, b❩, c)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a, b❩, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(a, ƒ❨b, c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨b, c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨a, b, c❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(a, c, b)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, c, b)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(a, ƒ❨c❩, b)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨c❩, b)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(a, c, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, c, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(a, ƒ❨c❩, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨c❩, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a, c❩, b)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a, c❩, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(a, ƒ❨c, b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨c, b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨a, c, b❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(b, a, c)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, a, c)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(b, ƒ❨a❩, c)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, ƒ❨a❩, c)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(b, a, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, a, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(b, ƒ❨a❩, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, ƒ❨a❩, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b, a❩, c)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b, a❩, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(b, ƒ❨a, c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, ƒ❨a, c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨b, a, c❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(b, c, a)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, c, a)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(b, ƒ❨c❩, a)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, ƒ❨c❩, a)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(b, c, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, c, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(b, ƒ❨c❩, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, ƒ❨c❩, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b, c❩, a)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b, c❩, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(b, ƒ❨c, a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, ƒ❨c, a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨b, c, a❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(c, a, b)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, a, b)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(c, ƒ❨a❩, b)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, ƒ❨a❩, b)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(c, a, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, a, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(c, ƒ❨a❩, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, ƒ❨a❩, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c, a❩, b)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c, a❩, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(c, ƒ❨a, b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, ƒ❨a, b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨c, a, b❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(c, b, a)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, b, a)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(c, ƒ❨b❩, a)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, ƒ❨b❩, a)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(c, b, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, b, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(c, ƒ❨b❩, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, ƒ❨b❩, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c, b❩, a)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c, b❩, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(c, ƒ❨b, a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, ƒ❨b, a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨c, b, a❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!(None, afac_generator.next());
  }


  #[test]
  fn generate_one_afa_application() {
    let children = vec!["ƒ", "a", "b", "c"].iter().map(|x| Symbol::from_static_str(x)).collect::<Vec<Atom>>();
    let f = Atom::SExpression(Rc::new(children));

    let mut afa_generator = AFAGenerator::<EnumerateOne>::new(f);

    assert_eq!("(a, b, c)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!(None, afa_generator.next());
  }

  #[test]
  fn generate_one_afac_application() {
    let children = vec!["ƒ", "a", "b", "c"].iter().map(|x| Symbol::from_static_str(x)).collect::<Vec<Atom>>();
    let f = Atom::SExpression(Rc::new(children));

    let mut afac_generator = AFACGenerator::<EnumerateOne>::new(f);

    assert_eq!("(a, b, c)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!(None, afac_generator.next());
  }


  #[test]
  fn generate_no_unapplied_afa_applications() {
    let children = vec!["ƒ", "a", "b", "c"].iter().map(|x| Symbol::from_static_str(x)).collect::<Vec<Atom>>();
    let f = Atom::SExpression(Rc::new(children));

    let mut afa_generator = AFAGenerator::<EnumerateNoUnapplied>::new(f);

    assert_eq!("(ƒ❨a❩, ƒ❨b❩, ƒ❨c❩)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(ƒ❨a, b❩, ƒ❨c❩)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨b, c❩)", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!("ƒ❨a, b, c❩", sequence_to_string(afa_generator.next().unwrap()));
    assert_eq!(None, afa_generator.next());
  }



  #[test]
  fn generate_no_unapplied_afac_applications() {
    let children = vec!["ƒ", "a", "b", "c"].iter().map(|x| Symbol::from_static_str(x)).collect::<Vec<Atom>>();
    let f = Atom::SExpression(Rc::new(children));

    let mut afac_generator = AFACGenerator::<EnumerateNoUnapplied>::new(f);

    // for res in afac_generator {
    //   println!("{}", res);
    // }
    assert_eq!("(ƒ❨a❩, ƒ❨b❩, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a, b❩, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨b, c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨a, b, c❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨c❩, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a, c❩, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨a❩, ƒ❨c, b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨a, c, b❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, ƒ❨a❩, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b, a❩, ƒ❨c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, ƒ❨a, c❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨b, a, c❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, ƒ❨c❩, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b, c❩, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨b❩, ƒ❨c, a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨b, c, a❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, ƒ❨a❩, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c, a❩, ƒ❨b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, ƒ❨a, b❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨c, a, b❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, ƒ❨b❩, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c, b❩, ƒ❨a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("(ƒ❨c❩, ƒ❨b, a❩)", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!("ƒ❨c, b, a❩", sequence_to_string(afac_generator.next().unwrap()));
    assert_eq!(None, afac_generator.next());
  }

}
