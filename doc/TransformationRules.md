# Transformation Rules for Match Equations

The algorithm proceeds by repeatedly applying transformation rules to the active match equation.
When there are no more match equations to solve, the algorithm terminates with success. When
no transformation rule applies to a match equation, the algorithm terminates with failure.

The table represents two distinct matching procedures according to whether associativity is strict or not.

## Table Form

| Name              | Description                                            |         Transformed Equation         | Resulting Equations Γ  |  Solution Set S  |
| ----------------- | ------------------------------------------------------ | :----------------------------------: | :--------------------: | :--------------: |
|                   |                                                        |                                      |                        |                  |
|                   | ***Common Rules***                                     |                                      |                        |                  |
| **T**             | Trivial                                                |                s ≪ᴱs                 |           ∅            |        ∅         |
| **IVE**           | Individual variable elimination                        |                 x≪ᴱt                 |           ∅            |       x≈t        |
| **FVE**           | Function variable elimination                          |              X(s̃)≪ᴱƒ(t̃)              |       ƒ(s̃)≪ᴱƒ(t̃)       |       X≈ƒ        |
|                   |                                                        |                                      |                        |                  |
|                   | ***Rules for free symbols***                           |                                      |                        |                  |
| **Dec-F**         | Decomposition under free head                          |            ƒ(s,s̃)≪ᴱƒ(t,t̃)            |  s≪ᴱt,<br> ƒ(s̃)≪ᴱƒ(t̃)  |        ∅         |
| **SVE-F**         | Sequence variable elimination under free head          |           ƒ(x̅,s̃)≪ᴱƒ(t̃₁,t̃₂)           |      ƒ(s̃)≪ᴱ ƒ(t̃₂)      |       x̅≈t̃₁       |
|                   |                                                        |                                      |                        |                  |
|                   | ***Rules for commutative symbols***                    |                                      |                        |                  |
| **Dec-C**         | Decomposition under commutative head                   |          ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂)          | s≪ᴱt<br>ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂) |        ∅         |
| **SVE-C**         | Sequence variable elimination under commutative head   | ƒ(x̅,,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) |  ƒ(s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)   |  x̅ ≈ ❴t₁,…,tₙ❵   |
|                   |                                                        |                                      |                        |                  |
|                   | ***Rules for associative symbols***                    |                                      |                        |                  |
| **Dec-A**         | Decomposition under associative head                   |            ƒ(s,s̃)≪ᴱƒ(t,t̃)            |   s≪ᴱt<br>ƒ(s̃)≪ᴱƒ(t̃)   |        ∅         |
| **SVE-A**         | Sequence variable elimination under associative head   |           ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t̃₂)           |      ƒ(̅s̃)≪ᴱ ƒ(t̃₂)      |    x≈(t̃₁)[ƒ]     |
| **FVE-A-strict**  | Function variable elimination under associative head   |          ƒ(X(s̃₁),s̃₂)≪ᴱƒ(t̃)           |     ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)     |       X≈ƒ        |
| **IVE-A-strict**  | Individual variable elimination under associative head |           ƒ(x,s̃)≪ᴱƒ(t̃₁,t̃₂)           |      ƒ(̅s̃)≪ᴱ ƒ(t̃₂)      |     x≈ƒ(t̃₁)      |
|                   |                                                        |                                      |                        |                  |
|                   | ***Rules for associative-commutative symbols***        |                                      |                        |                  |
| **Dec-AC**        | Decomposition under AC head (Same as Dec-C)            |          ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂)          | s≪ᴱt<br>ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂) |        ∅         |
| **SVE-AC**        | Sequence variable elimination under AC head            | ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁)  |  ƒ(̅s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)   | x̅ ≈ ❴t₁,…,tₙ❵[ƒ] |
| **FVE-AC-strict** | Function variable elimination under AC head            |          ƒ(X(s̃₁),s̃₂)≪ᴱƒ(t̃)           |     ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)     |     S={X≈ƒ}      |
| **IVE-AC**        | Individual variable elimination under AC head          | ƒ(x,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁)  |  ƒ(̅s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)   |  x ≈ ƒ(t₁,…,tₙ)  |
|                   |                                                        |                                      |                        |                  |



## List Form

### _Common Rules._

The common rules apply in any theory.

**T:** Trivial
s ≪ᴱs ⇝ᵩ ∅.

**IVE:** Individual variable elimination
x≪ᴱt⇝ₛ∅ where S ={x≈t}.

**FVE:** Function variable elimination
X(s̃)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃)≪ᴱƒ(t̃)}, where S={X≈ƒ}.

### _Rules for free symbols._

These rules apply when ƒ is free.

**Dec-F:** Decomposition under free head
ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)},
where ƒ is free and s∉Ꮙₛₑ.

**SVE-F:** Sequence variable elimination under free head
ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is free and S={x̅≈t̃₁}.
An SVE-F match generator must enumerate all possible ways of choosing t̃₁.

### _Rules for commutative symbols._

These rules apply when ƒ is commutative but not associative.

**Dec-C:** Decomposition under commutative head
ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)}
where ƒ is commutative but non-associative and s∉Ꮙₛₑ.
A Dec-C match generator must enumerate all possible ways of choosing t.

**SVE-C:** Sequence variable elimination under commutative head
ƒ(x̅,,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)}
where n ≥ 0, ƒ is commutative and non-associative,
S = {x̅ ≈ ❴t₁,…,tₙ❵ }.
An SVE-C match generator must enumerate all possible ways of choosing the
t-sequence. This is equivalent to enumerating all possible
subsets of a set with n elements, 2^n possibilities.

### _Rules for associative symbols._

These rules apply when ƒ is associative but not commutative.

**Dec-A:** Decomposition under associative head
ƒ(s,s̃)≪ᴱƒ(t,t̃) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃)}
where ƒ is associative but non-commutative and s∉Ꮙₛₑ.

**SVE-A:** Sequence variable elimination under associative head
ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is associative
and non-commutative and S={x≈(t̃₁)[ƒ]}.
An SVE-A match generator must enumerate all possible ways of choosing t̃₁.

**FVE-A-strict:** Function variable elimination under associative head
ƒ(X(s̃₁),s̃₂)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is associative
and non-commutative and S={X≈ƒ}. We require s̃≠().

**IVE-A-strict:** Individual variable elimination under associative head
ƒ(x,s̃)≪ᴱƒ(t̃₁,t̃₂) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₂)}, where ƒ is associative and
non-commutative and S = {x≈ƒ(t̃₁)}.  We require t̃₁≠().
IVE-A must enumerate all possible ways of choosing t̃₁.


### _Rules for associative-commutative symbols_.

These rules apply when ƒ is both associative and commutative.

**Dec-AC:** Decomposition under AC head
Same as Dec-C.
ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂) ⇝ᵩ {s≪ᴱt, ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂)} where ƒ is
associative-commutative and s∉Ꮙₛₑ.
Dec-AC must enumerate all possible ways of choosing t.

**SVE-AC:** Sequence variable elimination under AC head
Same as SVE-C except for substitutions in S.
ƒ(̅x,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)}
where n ≥ 0, ƒ is associative-commutative, and
S = {x̅ ≈ ❴t₁,…,tₙ❵[ƒ] }.
SVE-AC must enumerate all possible ways of choosing the
t-sequence. This is equivalent to enumerating all possible
subsets of a set with n elements, 2^n possibilities.

**FVE-AC-strict:** Function variable elimination under AC head
Same as FVE-A.
ƒ(X(s̃₁),s̃₂)≪ᴱƒ(t̃)⇝ₛ{ƒ(s̃₁,s̃₂)≪ᴱƒ(t̃)}, where ƒ is associative-
commutative and S={X≈ƒ}. We require s̃≠().

**IVE-AC:** Individual variable elimination under AC head
ƒ(x,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) ⇝ₛ {ƒ(̅s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)}
where n ≥ 0, ƒ is associative-commutative, and
S = {x ≈ ƒ(t₁,…,tₙ) }. We require n>0.
IVE-AC must enumerate all possible ways of choosing the
t-sequence. This is equivalent to enumerating all possible
subsets of a set with n elements, 2^n possibilities.

