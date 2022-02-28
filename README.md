# Lemur

### An experiment in pattern matching algorithms.

![Lemur](https://repository-images.githubusercontent.com/460711591/cffb54a0-00de-4a7b-bfd5-35dde4a62b73)

An implementation of the pattern matching algorithms described in the paper:

> Besik Dundua, Temur Kutsia, and Mircea Marin, _[Variadic equational matching in associative and commutative theories](http://www3.risc.jku.at/publications/download/risc_6260/variadic-equational-matching-jsc-final-with-mma-versions.pdf)_, Journal of Symbolic Computation, vol 106, 2021, p. 78-109

# The Algorithm

The algorithm described in the paper relies on repeated application of transformation rules to "match equations." We
first describe the algorithm before listing the rules.

## Data Generators and Structures

The central player in the algorithm is the `Matcher`, which roughly speaking
corresponds to a generator (in the software sense) of the substitutions generated
(in the mathematical sense) by a solved equation, Σ(eq). It is not precisely the
same, if I understand correctly, because a `Matcher` also generates substitutions
for every possible way that a rule can transform the same equation (instead of
choosing an alternative nondeterministically). `Matcher`s also generate the
corresponding matching equations, and `Matcher`s know how to "undo" whatever they
generated last (by popping things from stacks, described below).

We have the following stack structures:

  * The matching equation stack Γ
  * The substitution stack S
  * The `Matcher` stack

The equation (or `Matcher`) on the top of the equation stack (resp. `Matcher`
stack) is said to be the _active equation_ (resp. _active `Matcher`_).

## Algorithm in steps

Start state: S = Ø, Γ = {pattern ≪ expression}.

|      |      |      |                                                              |      |
| ---- | ---- | ---- | ------------------------------------------------------------ | ---- |
| 0.   |      |      | **Prepare the active matching equation.**                    |      |
|      |      |      | The equation at the top of the Γ stack is active. If the LHS (the pattern) of the matching equation is a named variable, query S to see if the variable has a substitution. If so, replace the variable with its substitution and continue. (I need to check that the stack order guarantees this substitution will be undone.) At most one transformation rule can apply. |      |
|      |      |      |                                                              |      |
| 1.   |      |      | **Act on the active equation.**                              |      |
|      | a.   |      | If no rule applies:                                          |      |
|      |      | i.   | If the matcher stack is empty, halt with **FAILURE**.        |      |
|      |      | ii.  | If there is an active match generator on top of the matcher stack, undo the actions of the last match generated from this `Matcher`:<br>&nbsp;&nbsp;- pop the top equations in Γ pushed by the last match;<br>&nbsp;&nbsp;- pop the top  substitutions in S pushed by the last match. |      |
|      | b.   |      | If a rule applies, create the `Matcher` for the rule, (provide it the equation), and push it into the `Matcher` stack. It is now the active `Matcher`. |      |
|      |      |      |                                                              |      |
| 2.   |      |      | **Request a new match.**                                     |      |
|      | a.   |      | If there is no active `Matcher` on top of the `Matcher` stack, return with **FAILURE**. |      |
|      | b.   |      | If there is an active `Matcher`, call `next()` on the active match generator. This<br/>generates zero or more substitutions which are stored in S (pushed onto the S<br/>stack) and zero or more matching equations which are stored in Γ. |      |
|      |      |      |                                                              |      |
| 3.   |      |      | **Act on the result of `next()`.**                           |      |
|      | a.   |      | If the match generator is exhausted (returns `None`), proceed to *Step 4.* |      |
|      | b.   |      | If Γ is empty, return with **SUCCESS**.                      |      |
|      | c.   |      | Otherwise, proceed to *Step 0.*                              |      |
|      |      |      |                                                              |      |
| 4.   |      |      | **Backtrack.**                                               |      |
|      |      |      | Same as *Step 1.a.ii*, but pop `Matcher` from the stack before proceeding to *Step 2*. |      |

To obtain additional matches upon success, proceed from Step 3.b to Step 1.a.ii.

## Transformation Rules for Match Equations

One can think of a match equation as an equation of the form `pattern = ground term`. A successful match of
`pattern` against the ground expression means solving the match equation for a substitution that transforms `pattern` into
`ground term`. As the algorithm progresses, match equations are simplified, broken into pieces, or eliminated (solved),
while individual variable substitutions are created. The set $S$ will contain the substitutions, while the set $\Gamma$
will hold the match equations. The context will determine if $S$ refers to all substitutions solving the
original equation, just the substitutions generated by a single rule application, or the substitutions that have been
generated up to a certain point in the running of the algorithm. Similarly for $\Gamma$.

| Name      | Description                                          |         Transformed Equation         | Resulting Equations Γ  | Solution Set S |
| --------- | ---------------------------------------------------- | :----------------------------------: | :--------------------: | :------------: |
|           | ***Common Rules***                                   |                                      |                        |                |
| **T**     | Trivial                                              |                s ≪ᴱs                 |           ∅            |       ∅        |
| **IVE**   | Individual variable elimination                      |                 x≪ᴱt                 |           ∅            |      x≈t       |
| **FVE**   | Function variable elimination                        |              X(s̃)≪ᴱƒ(t̃)              |       ƒ(s̃)≪ᴱƒ(t̃)       |      X≈ƒ       |
|           |                                                      |                                      |                        |                |
|           | ***Rules for free symbols***                         |                                      |                        |                |
| **Dec-F** | Decomposition under free head                        |            ƒ(s,s̃)≪ᴱƒ(t,t̃)            |  s≪ᴱt,<br> ƒ(s̃)≪ᴱƒ(t̃)  |       ∅        |
| **SVE-F** | Sequence variable elimination under free head        |           ƒ(x̅,s̃)≪ᴱƒ(t̃₁,t̃₂)           |      ƒ(s̃)≪ᴱ ƒ(t̃₂)      |      x̅≈t̃₁      |
|           |                                                      |                                      |                        |                |
|           | ***Rules for commutative symbols***                  |                                      |                        |                |
| **Dec-C** | Decomposition under commutative head                 |          ƒ(s,s̃)≪ᴱƒ(t̃₁,t,t̃₂)          | s≪ᴱt<br>ƒ(s̃)≪ᴱƒ(t̃₁,t̃₂) |                |
| **SVE-C** | Sequence variable elimination under commutative head | ƒ(x̅,,s̃)≪ᴱƒ(t̃₁,t₁,t̃₂,t₂,…,t̃ₙ,tₙ,t̃ₙ₊₁) |  ƒ(s̃)≪ᴱ ƒ(t̃₁,…,t̃ₙ₊₁)   | x̅ ≈ ❴t₁,…,tₙ❵  |
|           |                                                      |                                      |                        |                |
|           |                                                      |                                      |                        |                |
|           |                                                      |                                      |                        |                |
|           |                                                      |                                      |                        |                |



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
