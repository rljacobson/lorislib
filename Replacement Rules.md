## *Common Rules.*

The common rules apply in any theory.

### T: Trivial

s ≪ᴱs ⇝ᵩ ∅.

### IVE: Individual variable elimination

x≪ᴱt⇝ₛ∅ where S ={x≈t}.

### FVE: Function variable elimination

X(s̃)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃)≪ᴱƒ(t̃)}, where S={X≈ƒ}.

## *Rules for free symbols.*

These rules apply when ƒ is free.

### Dec-F: Decomposition under free head

ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)}, where ƒ is free and s∉Ꮙₛₑ.

### SVE-F: Sequence variable elimination under free head

ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is free and S={x≈t̃₁}

## *Rules for commutative symbols.*

These rules apply when f is commutative but not associative.

### Dec-C: Decomposition under commutative head

ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)} where ƒ is commutative but non-associative and s∉Ꮙₛₑ.

### SVE-C: Sequence variable elimination under commutative head

ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)} where n ≥ 0, ƒ is commutative and non-associative, and S = {x̅ ≈ ❴t₁,…,tₙ❵ }.

## *Rules for associative symbols.*

These rules apply when ƒ is associative but not commutative.

### Dec-A: Decomposition under associative head

ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)} where ƒ is associative but non-commutative and s∉Ꮙₛₑ.

### SVE-A: Sequence variable elimination under associative head

ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is associative and non-commutative and S={x≈(t̃₁)[ƒ]}.

### FVE-A: Function variable elimination under associative head

ƒ(X(s̃₁),s̃₁)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is associative and non-commutative and S={X≈ƒ}.

### IVE-A: Individual variable elimination under associative head

ƒ(x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is associative and non-commutative and S = {x≈ƒ(t̃₁)}.

## *Rules for associative-commutative symbols*.

These rules apply when ƒ is both associative and commutative.

### Dec-AC: Decomposition under AC head

ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)} where ƒ is associative-commutative and s∉Ꮙₛₑ.

### SVE-AC: Sequence variable elimination under AC head

ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)} where n ≥ 0, ƒ is associative-commutative, and S = {x̅ ≈ ❴t₁,…,tₙ❵[ƒ] }.

### FVE-AC: Function variable elimination under AC head

ƒ(X(s̃₁),s̃₁)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is associative-commutative and S={X≈ƒ}.