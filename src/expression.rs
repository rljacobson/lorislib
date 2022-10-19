/*!

An `Expression` is a syntactically correct "thing", a symbol, function, sequence, non-sequence variable,
or sequence variable. We try to keep `Expression`s immutable. We can use `Rc<Expression>`, aliased to
`RcExpression`, as a garbage collected copy-on-write smart pointer. Every `Expression` is a composition
of `Atoms`, so every `Expression` _is_ an atom, that is, has an atom as its root. Therefore, `Expression`
is an enum whose variants wrap each `Atom` type. We use `EnumDiscriminants` from `strum` to derive the
`ExpressionKind` enum whose variants are only the names (no data) of the variants in `Expression`.

We use `Expression` as an adapter from whatever expression tree scheme we want to the pattern matcher. It lets us
change the term rewriting system arbitrarily without needing to touch the pattern matcher. It is a mechanism for
decoupling.

See the `atoms` module for concrete implementations of the `Expression` variants.

    https://github.com/rust-lang/lang-team/issues/122#issuecomment-964459769
    "[I]t is a common, and annoying, pattern in Rust today to have to make a struct for every enum variant and then
    just have the enum wrap those structs. This gives you the ability to have a "type for an enum variant", but is
    annoying and inconvenient."

*/

use std::{
  rc::Rc,
  cmp::Ordering
};
use std::hash::{Hash, Hasher};

use strum::{EnumDiscriminants, Display};
use lazy_static::lazy_static;

use crate::{
  format::{
    Formattable,
    ExpressionFormatter
  },
  atom::{
    Atom
  },
  normal_form::NormalFormOrder,
  interner::InternedString,
};


pub type RcExpression = Rc<Expression>;

lazy_static!{
  static ref EMPTY_STRING: String = String::from("");
}


#[derive(Clone, PartialEq, Eq, EnumDiscriminants, Debug)]
#[strum_discriminants(name(ExpressionKind))]
#[strum_discriminants(derive(Display))]
pub enum Expression{
  /// A symbol is an atomic nonvariable expression.
  Symbol(Atom),

  /**
  A function is an M-expression. For the purposes of this library, the "head" of
  a function is not an expression. It's just the name of the function.
  Functions are usually written with parentheses, even if the function takes no
  arguments: `f()`. In contexts where only a function name can be the
  parentheses are dropped.
  */
  Function(Atom),

  /**
  A `Sequence` is an ordered list of expressions that can be spliced into a
  function's arguments or into another sequence. For clarity, `Sequence`s will
  always be written with parentheses, even if the sequence is empty: `()`, `(a,
  f(b), c)`, etc. A `Sequence` is a contiguous sublist of terms from a possibly
  larger list that we want to call out specifically for some purpose.
  */
  Sequence(Atom),

  /// A `Variable` is a placeholder for an atom and may be bound or unbound. It is not a variable in the mathematical
  /// sense. Rather, it is a metavariable, a variable for the purposes of pattern matching.
  Variable(Atom),

  /// A sequence variable is a placeholder for a sequence, that is, a variable that
  /// only holds sequences.
  SequenceVariable(Atom),

  StringLiteral(Atom),

  Integer(Atom),

  Real(Atom),
}


macro_rules! forward_call {
  ($func_name:ident, $ret_type:ty) => {
    // Note: we need self to be mutable so it can cache its own hash value.
    pub fn $func_name(&self) -> $ret_type {
      match self {
        // Expression::StringExpression(e) => e.$func_name(),
        | Expression::Symbol(e)
        | Expression::Function(e)
        | Expression::Sequence(e)
        | Expression::SequenceVariable(e)
        | Expression::Variable(e)
        | Expression::StringLiteral(e)
        | Expression::Integer(e)
        | Expression::Real(e)             => e.$func_name(),
      }
    }
  }
}


impl Expression {

  pub fn kind(&self) -> ExpressionKind {
    self.into()
  }


  /// Transforms self into associative normal form in-place.
  pub fn associative_normal_form(&mut self) {
    match self {

        Expression::Function(function) if function.associative()  => function.associative_normal_form(),

        Expression::Sequence(sequence) => sequence.associative_normal_form(),

        _ => { /* nothing to do */ }

    }
  }


  /// Transforms self into commutative normal form in-place.
  pub fn commutative_normal_form(&mut self) {
    match self {

      Expression::Function(function) if function.commutative() =>
        function.commutative_normal_form(),

      // It is not clear how to handle commutativity for sequences. For now, we will assume that
      // sequences are not commutative. That feels more conservative.
      // Expression::Sequence(sequence) => sequence.commutative_normal_form(),

      _ => { /* nothing to do */ }

    }
  }


  /// Transforms self into AC-normal form in-place.
  pub fn normal_form(&mut self) {
    self.associative_normal_form();
    self.commutative_normal_form();
  }

  /*
  fn copy(&self) -> Expression;
  fn needs_eval(&self) -> bool;
  */

  // fn deep_copy(&self) -> Expression;
  // forward_call!(deep_copy, Expression);
  forward_call!(hash, u64);

  forward_call!(name, Option<InternedString>);
  forward_call!(len, usize);
  forward_call!(is_empty, bool);

}


impl Formattable for Expression {

  fn format(&self, formatter: &ExpressionFormatter) -> String {
    match self {
      Expression::Symbol(e)
      | Expression::Function(e)
      | Expression::Sequence(e)
      | Expression::Variable(e)
      | Expression::SequenceVariable(e)
      | Expression::StringLiteral(e)
      | Expression::Integer(e)
      | Expression::Real(e) => e.format(formatter)
    }
  }

}


impl NormalFormOrder for Expression {
  fn cmp(&self, other: &Self) -> Ordering {
    match (self, other) {

      // Same expression type //

      (Expression::Symbol(s), Expression::Symbol(t))
      => NormalFormOrder::cmp(s, t),

      (Expression::StringLiteral(s), Expression::StringLiteral(t))
      => NormalFormOrder::cmp(s, t),

      (Expression::Function(f), Expression::Function(g))
      => NormalFormOrder::cmp(f, g),

      (Expression::Variable(v), Expression::Variable(u))
      => NormalFormOrder::cmp(v, u),

      (Expression::Sequence(s), Expression::Sequence(t))
      => NormalFormOrder::cmp(s, t),

      (Expression::SequenceVariable(v), Expression::SequenceVariable(u))
      => NormalFormOrder::cmp(v, u),

      // Different expression types //
      // Symbol < Function < Sequence < Variable < SequenceVariable
      (thing_one, thing_two) => {
        if Into::<ExpressionKind>::into(thing_one) as u32
            > Into::<ExpressionKind>::into(thing_two) as u32
        {
          Ordering::Greater
        } else {
          Ordering::Less
        }
      } // end match on (thing_one, thing_two)

    } // end match (self, other)
  }
}


impl Hash for Expression {
  fn hash<H: Hasher>(&self, state: &mut H) {
    state.write_u64(self.hash())
  }
}


impl From<Atom> for Expression {
  fn from(atom: Atom) -> Self {
    match atom {
      Atom::String(_) => Expression::StringLiteral(atom),
      Atom::Integer(_) => Expression::Integer(atom),
      Atom::Real(_) => Expression::Real(atom),
      Atom::Symbol(_) => Expression::Symbol(atom),
      Atom::SExpression(_) => Expression::Function(atom),
    }
  }
}

display_formattable_impl!(Expression);
