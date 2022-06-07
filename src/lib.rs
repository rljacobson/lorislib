#![feature(toowned_clone_into)]
#![feature(type_alias_impl_trait)]
#![allow(dead_code)]

#[macro_use]
mod format;
pub mod expression;
mod logging;
mod normal_form;
mod attributes;
mod atoms;
mod matching;
mod context;
#[cfg(feature = "nom")]
mod parser;
mod data_structures;


/*

We use the strict associative variants of these rules, which results in a finitary matching theory.

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
An SVE-F match generator must enumerate all possible ways of choosing t̃₁.

_Rules for commutative symbols._
These rules apply when ƒ is commutative but not associative.

Dec-C: Decomposition under commutative head
ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)}
where ƒ is commutative but non-associative and s∉Ꮙₛₑ.
A Dec-C match generator must enumerate all possible ways of choosing t.

SVE-C: Sequence variable elimination under commutative head
ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)}
where n ≥ 0, ƒ is commutative and non-associative,
S = {x̅ ≈ ❴t₁,…,tₙ❵ }.
An SVE-C match generator must enumerate all possible ways of choosing the
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
An SVE-A match generator must enumerate all possible ways of choosing t̃₁.

FVE-A-strict: Function variable elimination under associative head
ƒ(X(s̃₁),s̃₂)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is associative
and non-commutative and S={X≈ƒ}. We require s̃≠().

IVE-A-strict: Individual variable elimination under associative head
ƒ(x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is associative and
non-commutative and S = {x≈ƒ(t̃₁)}.  We require t̃₁≠().
IVE-A must enumerate all possible ways of choosing t̃₁.


_Rules for associative-commutative symbols_.
These rules apply when ƒ is both associative and commutative.

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

FVE-AC-strict: Function variable elimination under AC head
Same as FVE-A.
ƒ(X(s̃₁),s̃₂)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is associative-
commutative and S={X≈ƒ}. We require s̃≠().

IVE-AC: Individual variable elimination under AC head
ƒ(x,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)}
where n ≥ 0, ƒ is associative-commutative, and
S = {x ≈ ƒ(t₁,…,tₙ) }. We require n>0.
IVE-AC must enumerate all possible ways of choosing the
t-sequence. This is equivalent to enumerating all possible
subsets of a set with n elements, 2^n possibilities.

*/



#[cfg(test)]
mod tests {
  // use super::*;

  #[test]
  fn it_works() {
    let result = 2 + 2;
    assert_eq!(result, 4);
  }
}
