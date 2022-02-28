/*!

## *Rules for associative-commutative symbols*.

These rules apply when ƒ is both associative and commutative.

### Dec-AC: Decomposition under AC head

ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)} where ƒ is
associative-commutative and s∉Ꮙₛₑ.

### SVE-AC: Sequence variable elimination under AC head

ƒ(x&#773;,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁)
  ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)} where n ≥ 0, ƒ is
associative-commutative, and S = {x&#773; ≈ ❴t₁,…,tₙ❵[ƒ] }.

### FVE-AC: Function variable elimination under AC head

ƒ(X(s̃₁),s̃₁)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is
associative-commutative and S={X≈ƒ}.

*/

use super::{
  commutative::RuleDecC,
  function_application::{
    AFACGenerator,
    EnumerateAll,
    RuleSVE
  },
  associative::RuleFVEA
};

/// Dec-AC: Decomposition under AC head
/// ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)}
/// where ƒ is associative-commutative and s∉Ꮙₛₑ.
/// Identical to `RuleDecC`, decomposition under commutative head.
pub type RuleDecAC = RuleDecC;

/// Sequence variable elimination under AC head
/// ƒ(x̅,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ
///   {ƒ(s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)}
/// where n ≥ 0, ƒ is associative-commutative, and
///   S = {x̅ ≈ ❴t₁,…,tₙ❵[ƒ] }.
pub type RuleSVEAC = RuleSVE<AFACGenerator<EnumerateAll>>;

/// Function variable elimination under AC head
/// ƒ(X(s̃₁),s̃₁)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ
/// is associative-commutative and S={X≈ƒ}.
/// Same as `RuleFVEA`.
pub type RuleFVEAC = RuleFVEA;
