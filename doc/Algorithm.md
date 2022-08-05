# Data Generators and Structures

The central player in the algorithm is the `MatchGenerator`, which roughly speaking
corresponds to a generator (in the software sense) of the substitutions generated
(in the mathematical sense) by a solved equation, Σ(eq). It is not precisely the
same, if I understand correctly, because a `MatchGenerator` also generates substitutions
for every possible way that a rule can transform the same equation (instead of
choosing an alternative nondeterministically). `MatchGenerator`s also generate the
corresponding matching equations, and `MatchGenerator`s know how to "undo" whatever they
generated last (by popping things from stacks, described below).

We have the following stack structures:

  * The matching equation stack Γ
  * The substitution stack S
  * The match stack

The equation (or match) on the top of the equation stack (resp. match
stack) is said to be the _active equation_ (resp. _active match generator_).

# Algorithm

Start state: S = Ø, Γ = {pattern ≪ expression}.

|      |      |      |                                                              |      |
| ---- | ---- | ---- | ------------------------------------------------------------ | ---- |
| 0.   |      |      | **Prepare the active matching equation.**                    |      |
|      |      |      | The equation at the top of the Γ stack is active. If the LHS (the pattern) of the matching equation is a named variable, query S to see if the variable has a substitution. If so, replace the variable with its substitution and continue. (I need to check that the stack order guarantees this substitution will be undone.) At most one transformation rule can apply. |      |
|      |      |      |                                                              |      |
| 1.   |      |      | **Act on the active equation.**                              |      |
|      | a.   |      | If no rule applies:                                          |      |
|      |      | i.   | If the match stack is empty, halt with **FAILURE**.        |      |
|      |      | ii.  | If there is an active match generator on top of the match stack, undo the actions of the last match generated from this `MatchGenerator`:<br>&nbsp;&nbsp;- pop the top equations in Γ pushed by the last match;<br>&nbsp;&nbsp;- pop the top  substitutions in S pushed by the last match. |      |
|      | b.   |      | If a rule applies, create the `MatchGenerator` for the rule, (provide it the equation), and push it into the match stack. It is now the active `MatchGenerator`. |      |
|      |      |      |                                                              |      |
| 2.   |      |      | **Request a new match.**                                     |      |
|      | a.   |      | If there is no active `MatchGenerator` on top of the match stack, return with **FAILURE**. |      |
|      | b.   |      | If there is an active `MatchGenerator`, call `next()` on the active match generator. This<br/>generates zero or more substitutions which are stored in S (pushed onto the S<br/>stack) and zero or more matching equations which are stored in Γ. |      |
|      |      |      |                                                              |      |
| 3.   |      |      | **Act on the result of `next()`.**                           |      |
|      | a.   |      | If the match generator is exhausted (returns `None`), proceed to *Step 4.* |      |
|      | b.   |      | If Γ is empty, return with **SUCCESS**.                      |      |
|      | c.   |      | Otherwise, proceed to *Step 0.*                              |      |
|      |      |      |                                                              |      |
| 4.   |      |      | **Backtrack.**                                               |      |
|      |      |      | Same as *Step 1.a.ii*, but pop `MatchGenerator` from the stack before proceeding to *Step 2*. |      |

To obtain additional matches upon success, proceed from Step 3.b to Step 1.a.ii.

