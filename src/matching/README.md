# Lemur

### An experiment in pattern matching algorithms.

![Lemur](https://repository-images.githubusercontent.com/460711591/cffb54a0-00de-4a7b-bfd5-35dde4a62b73)

An implementation of the pattern matching algorithms described in the paper:

> Besik Dundua, Temur Kutsia, and Mircea Marin, 
> [Variadic equational matching in associative and commutative theories](http://www3.risc.jku.at/publications/download/risc_6260/variadic-equational-matching-jsc-final-with-mma-versions.pdf)_, 
> Journal of Symbolic Computation, vol 106, 2021, p. 78-109

# The Algorithm

We implement algorithms **LM** (_Linear Matching_) and **LM**$_{\text{S}}$ (_Linear Matching with
Strict associativity_) as described in the paper with a minor modification to **LM** to make it
[finitary](doc/Glossary.md). The algorithm relies on repeated application of transformation rules to "match
equations." The algorithm is described in [doc/Algorithm.md](doc/Algorithm.md). The transformation rules are
detailed in [src/rules.rs](src/rules.rs). The algorrithm $M_{\text{MMA}}$, which captures the semantics of
Wolfram Mathematica's matching behavior, is not implemented, but I would like to implement it in the future.

Algorithms $RS$ (_Reconstruct Solutions_) and $RS_S$ (_Reconstruct Solutions
with Strict associativity_) are not implemented. Instead, match generators and
backtracking are used to find solutions. I would like to implement them in the future.
