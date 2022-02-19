mod formatter;
pub mod expression;
mod normal_form;
mod attributes;
mod atoms;

/**

A `MatchState` holds the state of the matching algorithm as it walks the
expression tree looking for a match. For example, a subexpression can be wrapped
in `HoldPattern`, which affects how the match is performed against pattern
symbols. Inside of `HoldPattern`, pattern symbols are treated as literal symbols,
not as patterns.

*/
// struct MatchState {}

/**

A `Matcher` enumerates every possible way for the pattern it represents to match
against the subject. The number of possible ways to match can be exponential in
the length of the pattern.

For example, matching `x__` in the pattern `f[x__, y__]` against `f[a, b, c, d]` for a commutative
function `f` enumerates all subsets of the set of symbols `{a, b, c, d}`. There
are $2^4$ such subsets. For `n` symbols, there are $2^n$ subsets. Even if one
only wants a single match to a pattern, it is possible that every match of a
constituent subpattern will need to be attempted before the first match of the
pattern is found.

Variadic associative, commutative, and associative-commutative matchings are
NP-complete problems.

*/
// enum Matcher {}

  /*
  _Common Rules._
  The common rules apply in any theory.

  T: Trivial
  s ≪ᴱs ⇝ᵩ ∅.

  IVE: Individual variable elimination
  x≪ᴱt⇝ₛ∅ where S ={x≈t}.

  FVE: Function variable elimination
  X(s̃)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃)≪ᴱƒ(t̃)}, where S={X≈ƒ}.

  _Rules for free symbols._
  These rules apply when ƒ is free.

  Dec-F: Decomposition under free head
  ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)},
  where ƒ is free and s∉Ꮙₛₑ.

  SVE-F: Sequence variable elimination under free head
  ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is free and S={x̅≈t̃₁}.
  An SVE-F matcher must enumerate all possible ways of choosing t̃₁.

  _Rules for commutative symbols._
  These rules apply when ƒ is commutative but not associative.

  Dec-C: Decomposition under commutative head
  ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)}
  where ƒ is commutative but non-associative and s∉Ꮙₛₑ.
  A Dec-C matcher must enumerate all possible ways of choosing t.

  SVE-C: Sequence variable elimination under commutative head
  ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)}
  where n ≥ 0, ƒ is commutative and non-associative,
  S = {x̅ ≈ ❴t₁,…,tₙ❵ }.
  An SVE-C matcher must enumerate all possible ways of choosing the
  t-sequence. This is equivalent to enumerating all possible
  subsets of a set with n elements, 2^n possibilities.


  _Rules for associative symbols._
  These rules apply when ƒ is associative but not commutative.

  Dec-A: Decomposition under associative head
  ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)}
  where ƒ is associative but non-commutative and s∉Ꮙₛₑ.

  SVE-A: Sequence variable elimination under associative head
  ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is associative
  and non-commutative and S={x≈(t̃₁)[ƒ]}.
  An SVE-A matcher must enumerate all possible ways of choosing t̃₁.

  FVE-A: Function variable elimination under associative head
  ƒ(X(s̃₁),s̃₁)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is associative
  and non-commutative and S={X≈ƒ}.

  IVE-A: Individual variable elimination under associative head
  ƒ(x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is associative and
  non-commutative and S = {x≈ƒ(t̃₁)}.
  IVE-A must enumerate all possible ways of choosing t̃₁.


  _Rules for associative-commutative symbols_. These rules apply
  when ƒ is both associative and commutative.

  Dec-AC: Decomposition under AC head
  Same as Dec-C.
  ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)} where ƒ is
  associative-commutative and s∉Ꮙₛₑ.
  Dec-AC must enumerate all possible ways of choosing t.

  SVE-AC: Sequence variable elimination under AC head
  Same as SVE-C except for substitutions in S.
  ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)}
  where n ≥ 0, ƒ is associative-commutative, and
  S = {x̅ ≈ ❴t₁,…,tₙ❵[ƒ] }.
  SVE-AC must enumerate all possible ways of choosing the
  t-sequence. This is equivalent to enumerating all possible
  subsets of a set with n elements, 2^n possibilities.

  FVE-AC: Function variable elimination under AC head
  Same as FVE-A.
  ƒ(X(s̃₁),s̃₁)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is associative-
  commutative and S={X≈ƒ}.

  IVE-AC: Individual variable elimination under AC head
  ƒ(x,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)}
  where n ≥ 0, ƒ is associative-commutative, and
  S = {x ≈ ƒ(t₁,…,tₙ) }.
  IVE-AC must enumerate all possible ways of choosing the
  t-sequence. This is equivalent to enumerating all possible
  subsets of a set with n elements, 2^n possibilities.

*/




// This is a concrete instance of the Solved Set in Dundua.
// struct PatternBindings{}



#[cfg(test)]
mod tests {
  // use super::*;

  #[test]
  fn it_works() {
    let result = 2 + 2;
    assert_eq!(result, 4);
  }
}
