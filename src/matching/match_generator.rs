/*!

A `MatchGenerator` enumerates every possible way for the pattern it represents to match
against the subject. A `MatchGenerator` corresponds to a "solved equation" in Dundua
(Def. 3, p. 10), denoted by `S`. We refer to matchers according to the rule in
Dundua they correspond to or to the pattern object they represent when there is
no ambiguity in doing so. The rules guarantee that there is only one choice of
match generator at any given point in the algorithm.

For some patterns (e.g. literal patterns), there is only one possible
substitution. For others, there are multiple possible substitutions.

> All sequence variable elimination and individual variable elimination rules
> [transform the equation in multiple ways], depending on the choice of the
> subsequence of the right hand side they match to. Also, Dec-C and Dec-AC rules
> may choose the `t` from the right hand side in different ways

Since future rule applications depend on this choice of how to transform the
equation, the set `S` is actually a stack. When a match generator is exhausted, it is
popped from the stack, and the next match generator is queried for the next substitution.

The number of possible ways to match can be exponential in the length of the
pattern. For example, matching `x__` in the pattern `f[x__, y__]` against `f[a,
b, c, d]` for a commutative function `f` enumerates all subsets of the set of
symbols `{a, b, c, d}`. There are $2^4$ such subsets. For `n` symbols, there are
$2^n$ subsets. Even if one only wants a single match to a pattern, it is possible
that every match of a constituent subpattern will need to be attempted before the
first match of the pattern is found.

Variadic associative, commutative, and associative-commutative matchings are
NP-complete problems.

*/

use std::fmt::Display;

use smallvec::SmallVec;

use crate::atom::Atom;
use super::{
  MatchEquation,
  Substitution
};


pub type NextMatchResultList  = SmallVec<[NextMatchResult; 3]>;
pub type MaybeNextMatchResult = Option<NextMatchResultList>;

/// A `MatchGenerator` iterates over every way it can transform a match equation and
/// every solution generated by that transformation. The iterator returns a
/// pair `(Γ, S)`, where Γ is a possibly empty set of match equations it
/// produces by consuming the active match equation, and S is a set of
/// substitutions. As it happens, the rules generate at most one substitution
/// at a time.
pub trait MatchGenerator: Iterator<Item=NextMatchResultList>{

  // Every match generator must also have a static method `try rule` that checks if it
  // applies to the active match equation and, if it does, returns an
  // instance of itself. Unfortunately, static methods cannot be used with
  // trait objects, and since this static method must return a type that
  // implements `MatchGenerator`, not a `MatchGenerator` trait object, I don't see a way
  // to do this. Traits are quite limited.

  // fn try_rule(match_equation: &MatchEquation) -> Option<Self>;

  /// Returns the match equation that this match generator was created to solve.
  fn match_equation(&self) -> MatchEquation;
}


pub enum NextMatchResult {
  MatchEquation(MatchEquation),
  Substitution(Substitution)
}

impl NextMatchResult{
  pub fn eq(pattern: Atom, ground: Atom) -> NextMatchResult {

    NextMatchResult::MatchEquation(
      MatchEquation{
        pattern,
        ground
      }
    )

  }

  pub fn sub(variable: Atom, ground: Atom) -> NextMatchResult {
    NextMatchResult::Substitution(
      Substitution{
        variable,
        ground,
      }
    )
  }
}


impl Display for NextMatchResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
          NextMatchResult::MatchEquation(me) => me.fmt(f),
          NextMatchResult::Substitution(sub) => sub.fmt(f),
        }
    }
}
