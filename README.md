# Loris

### An experiment in pattern matching algorithms.

<img src="loris.jpg" alt="Loris" style="zoom: 33%;" />

An implementation of the pattern matching algorithms described in the paper:

> Besik Dundua, Temur Kutsia, and Mircea Marin, 
> [Variadic equational matching in associative and commutative theories](http://www3.risc.jku.at/publications/download/risc_6260/variadic-equational-matching-jsc-final-with-mma-versions.pdf)_, 
> Journal of Symbolic Computation, vol 106, 2021, p. 78-109

See the front end [Loris](https://github.com/rljacobson/loris) for more details. 


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

# The Slow Loris

The Slow Loris is at risk of extinction due to habitat loss and the illegal wildlife trade. There is demand for 
lorises for use in traditional medicine and as pets. 
