/*

# Normalization

Dundua et al describe a formal framework for matching in associative and commutative
theories. A key component of their system is a normal form for terms. The
ordering of function symbols, terms, and term sequences is arbitrary but fixed.

> An _associative normal form_ (A-normal form) of a term or a sequence is obtained
> by rewriting it with the associativity axiom from left to right as long as
> possible. …

> We introduce a strict total order on function symbols and extend it to ground
> terms and term sequences so that the obtained ordering is also total. A
> commutative normal form (C-normal form) of a ground term is obtained by
> rearranging arguments of commutative function symbols to obtain the minimal term
> with respect to the defined ordering.

The system does not account for distributive functions, so mathematical
expressions (for example) are not semantically unique w.r.t. normal form. They
are only unique w.r.t. the chosen well-founded total ordering, associativity and
commutativity. My mental model is to think of it as an extension of lexicographic
ordering.

The matching algorithm for commutative and associative matching requires that
expressions be in _C-normal form_ (for commutative), _A-normal form_ (for
associative), or _AC-normal form_ (for both), depending on the type of the
expression and role it serves in the algorithm. We will just say normal form
instead of AC-normal form.

*/

use std::cmp::Ordering;

/// A total order on all functions, symbols, variables, and terms.
///
/// The total ordering of symbols does not use Rust's in-built `Ord` trait, because
/// implementors may have a different ordering that is natural for the type, and
/// normalization does not require Rust's ordering machinery.
pub trait NormalFormOrder {
  fn cmp(&self, other: &Self) -> Ordering;

  fn is_equal(&self, other: &Self) -> bool {
    // where T: NormalFormOrder {
      self.cmp(other) == Ordering::Equal
  }

  fn is_greater(&self, other: &Self) -> bool {
    // where T: NormalFormOrder {
      self.cmp(other) == Ordering::Greater
  }

  fn is_less(&self, other: &Self) -> bool {
    // where T: NormalFormOrder {
      self.cmp(other) == Ordering::Less
  }
}
