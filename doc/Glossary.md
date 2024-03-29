# Glossary of Terms

|                                       |                                                              |
| ------------------------------------- | :----------------------------------------------------------- |
| **Equational&nbsp;Theory**            | The set of axioms (e.g. commutativity, associativity) determine the *equational theory* in which the  matching occurs. |
| **Infinitary**                        | In some equational theories there exist match equations that admit an infinite number of solutions. These equational theories are called *infinitary*. |
| **Finitary**                          | An equational theory that is not infinitary is called *finitary*. In a finitary theory all solution sets are finite. |
| **Matching&nbsp;Procedure**           | The transformation rules (with the algorithm) determine the *matching procedure*. |
| **Complete**                          | A matching procedure that is always able to find every solution to a match equation is called *complete*. |
| **Incomplete**                        | Otherwise it is called *incomplete*.                         |
| **Variadic&nbsp;Function**            | A function that takes any finite number of arguments.        |
| **Variadic Associative Axiom**        | ƒ(x̅, ƒ(y̅), z̅) = ƒ(x̅, y̅, z̅).<br>If ƒ is associative we write A(ƒ). Note that  y̅ is allowed to be the empty sequence. |
| **Variadic Strict-Associative Axiom** | In Dundua, the strict associativity axiom is<br>   ƒ(x̅, ƒ(y̅₁, y, y̅₂), z̅) = ƒ(x̅, y̅₁, y, y̅₂, z̅), <br>that is, a term must appear inside the inner function in order to flatten it. Likewise, strict variants of the Σ expansion rules preclude producing the empty sequence. If ƒ is strict associative we write SA(ƒ). |
| **Variadic Commutative Axiom**        | ƒ(x̅, x, y̅, y, z̅) =  ƒ(x̅, y, y̅, x, z̅).<br>If ƒ is commutative we write C(ƒ). |
| **Flat Theory**                       | In Dundua *flat* is used as a synonym for variadic associative. This is not so in general. |
| **Linear Matching Problem**           | A matching problem in which no variable occurs more than once. |
| **Nonlinear Matching Problem**        | A matching problem in which some variable(s) occur(s) more than once. |
| **E-matchers**                        | A *substitution*, a mapping from individual variables to individual terms, from sequence variables to finite sequences of sequence elements, and from function variables to function symbols or function variables, such that all but finitely many variables are mapped to themselves. |
| **Minimal set of E-matchers**         | Any two distinct elements of S are incomparable with respect to ≤·. In other words, no two distinct substitutions match against each other, that is, no substitution is *more general* than another distinct substitution. |
|                                       |                                                              |
|                                       |                                                              |

