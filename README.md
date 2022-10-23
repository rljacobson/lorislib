# Loris

### A Term Rewriting and Computer Algebra System

Loris is a term rewriting and computer algebra system based on pattern matching algorithms developed by Besik 
Dundua, Temur Kutsia, and Mircea Marin. (See below.) To my knowledge, this is the first and only implementation of 
these algorithms. 

This repository is for lorislib, the library that implements almost all of Loris. There is also a front end: 
[Loris-CLI](https://github.com/rljacobson/loris_cli). When I make a repository for the project as a whole that brings in 
lorislib and loris_cli as git submodules, it will be located here: https://github.com/rljacobson/loris.


## Building & Using

You will need [Loris-CLI](https://github.com/rljacobson/loris_cli). Follow the build instructions there. 

Loris uses syntax similar to Mathematica:

```mma
f[x_] := 1 + x^2
```

You can think of Loris as an implementation of Wolfram Language. Only a handful of built-ins and predefined 
functions exist so far. Expect only basic arithmetic functions and system-related built-ins to work. However, it is 
nearing the point where it has enough built-ins to implement a powerful CAS in its own language. Source files for 
this implementation will accrue in [`lib/`](./lib/).

Another major limitation is that the matcher only has linear matching implemented so far, meaning that a variable can
only appear once on the LHS of a function definition. To get around this limitation, you can include a 
`Condition` in your definition: `f[x_, y_] := expr /; condition`. Here is a simplification rule (using `UpSet`) 
that employs this workaround:

```mma
a_*x_ + b_*y_ ^:= (a + b)*x /; And[SameQ[x, y], NumberQ[a], NumberQ[b]]
```
When I implement Algorithm $M$ from [Dundua et al, 2021], this limitation will be removed.

# An experiment in pattern matching algorithms.

<img src="loris.jpg" alt="Loris" style="zoom: 33%;" />

Loris started as an implementation of the pattern matching algorithms described in the paper:

> Besik Dundua, Temur Kutsia, and Mircea Marin, 
> _[Variadic equational matching in associative and commutative theories](http://www3.risc.jku.at/publications/download/risc_6260/variadic-equational-matching-jsc-final-with-mma-versions.pdf)_, 
> Journal of Symbolic Computation, vol 106, 2021, p. 78-109


## The Algorithm

We implement algorithms **LM** (_Linear Matching_) and **LM**$_{\text{S}}$ (_Linear Matching with
Strict associativity_) as described in the paper with a minor modification to **LM** to make it
[finitary](doc/Glossary.md). The algorithm relies on repeated application of transformation rules to "match
equations." The algorithm is described in [doc/Algorithm.md](doc/Algorithm.md). The transformation rules are
listed in [doc/TransformationRules.md](doc/TransformationRules.md) and implemented in the files in 
[src/matching/](src/matching/). The algorithm $M_{\text{MMA}}$, which captures the semantics of
Wolfram Mathematica's matching behavior, is not implemented, but I would like to implement it in the future.

Algorithms $RS$ (_Reconstruct Solutions_) and $RS_S$ (_Reconstruct Solutions
with Strict associativity_) are not implemented. Instead, match generators and
backtracking are used to find solutions. I would like to implement them in the future.

# License

Copyright (C) 2022 Robert Jacobson. This software is distributed under the 2-Clause BSD License.

The source code of the [permutation-generator](https://crates.io/crates/permutation-generator) crate by Thomas
Villa has been included in its entirety in `lorislib/src/matching/permutation_generator`. The permutaton-generator
crate is distributed under the MIT license.

# Contributing

Feel free to contribute. I am happy to take PRs. Unfortunately, I generally have so much happening in my life that I 
cannot offer support for my software projects on GitHub. Feel free to fork the project, though.

# The Slow Loris

The Slow Loris is at risk of extinction due to habitat loss and the illegal wildlife trade. There is demand for
lorises for use in traditional medicine and as pets. 
