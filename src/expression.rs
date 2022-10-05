/*!

An `Expression` is a syntactically correct "thing", a symbol, function, sequence, non-sequence variable,
or sequence variable. We try to keep `Expression`s immutable. We can use `Rc<Expression>`, aliased to
`RcExpression`, as a garbage collected copy-on-write smart pointer. Every `Expression` is a composition
of `Atoms`, so every `Expression` _is_ an atom, that is, has an atom as its root. Therefore, `Expression`
is an enum whose variants wrap each `Atom` type. We use `EnumDiscriminants` from `strum` to derive the
`ExpressionKind` enum whose variants are only the names (no data) of the variants in `Expression`.

To implement matching on your own structures, implement a `get_expression`
method or equivalent that returns the expression form of the type. Match on
the expression, and transform the result back into your native types.

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
    Formatter
  },
  atoms::{
    Symbol,
    Function,
    Variable,
    Sequence,
    SequenceVariable,
    StringLiteral,
    Atom,
    Integer,
    Real
  },
  normal_form::NormalFormOrder,
};


pub type RcExpression = Rc<Expression>;

lazy_static!{
  static ref EMPTY_STRING: String = String::from("");
}
// static EMPTY_STRING: String = String::from("");



#[derive(Clone, PartialEq, Eq, EnumDiscriminants, Debug)]
#[strum_discriminants(name(ExpressionKind))]
#[strum_discriminants(derive(Display))]
pub enum Expression{
  /// A symbol is an atomic nonvariable expression.
  Symbol(Symbol),

  /**
  A function is an M-expression. For the purposes of this library, the "head" of
  a function is not an expression. It's just the name of the function.
  Functions are usually written with parentheses, even if the function takes no
  arguments: `f()`. In contexts where only a function name can be the
  parentheses are dropped. See `crate::atoms::function` for more details.
  */
  Function(Function),

  /**
  A `Sequence` is an ordered list of expressions that can be spliced into a
  function's arguments or into another sequence. For clarity, `Sequence`s will
  always be written with parentheses, even if the sequence is empty: `()`, `(a,
  f(b), c)`, etc. A `Sequence` is a contiguous sublist of terms from a possibly
  larger list that we want to call out specifically for some purpose. See
  `crate::atomes::Sequence` for more details.
  */
  Sequence(Sequence),

  /// A `Variable` is a placeholder for an atom and may be bound or unbound. It is not a variable in the mathematical
  /// sense. Rather, it is a metavariable, a variable for the purposes of pattern matching.
  Variable(Variable),

  /// A sequence variable is a placeholder for a sequence, that is, a variable that
  /// only holds sequences.
  SequenceVariable(SequenceVariable),

  /// A wrapper for `String`
  StringLiteral(StringLiteral),

  Integer(Integer),

  Real(Real),
}


macro_rules! forward_call {
  ($func_name:ident, $ret_type:ty) => {
    // Note: we need self to be mutable so it can cache its own hash value.
    pub fn $func_name(&self) -> $ret_type {
      match self {
        // Expression::StringExpression(e) => e.$func_name(),
        Expression::Symbol(e)           => e.$func_name(),
        Expression::Function(e)         => e.$func_name(),
        Expression::Sequence(e)         => e.$func_name(),
        Expression::SequenceVariable(e) => e.$func_name(),
        Expression::Variable(e)         => e.$func_name(),
        Expression::StringLiteral(e)    => e.$func_name(),
        Expression::Integer(e)          => e.$func_name(),
        Expression::Real(e)             => e.$func_name(),
      }
    }
  }
}


impl Expression {

  pub fn kind(&self) -> ExpressionKind {
    self.into()
  }

  pub fn name(&self) -> &String {
    match self {
      Expression::Function(Function{ head, .. }) => {
        match (*head).as_ref() {

          // An argument can be made that we should format a variable function name.
          | Expression::Symbol(Symbol(name))// => &name,
          | Expression::Variable(Variable(name)) => &name,
          _ => &EMPTY_STRING
          // _ => unreachable!()

        }
      },

      | Expression::Sequence(_)
      | Expression::Integer(_)
      | Expression::Real(_)
      | Expression::StringLiteral(_) => &EMPTY_STRING,

      Expression::SequenceVariable(SequenceVariable(name)) => &name,
      Expression::Symbol(Symbol(name)) => &name,
      Expression::Variable(Variable(name)) => &name,

    }
  }

  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  pub fn len(&self) -> usize {
    match self {

      // Todo: Should non M-expressions have a positive length?
      | Expression::Symbol(_)
      | Expression::StringLiteral(_)
      | Expression::Variable(_)
      | Expression::SequenceVariable(_)
      | Expression::Integer(_)
      | Expression::Real(_)      => 0,

      Expression::Function(function) => function.len(),

      Expression::Sequence(sequence) => sequence.len(),

    }
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
  forward_call!(deep_copy, Expression);
  forward_call!(hash, u64);

}


impl Formattable for Expression {

  // forward_call!(format, String)
  fn format(&self, formatter: &Formatter) -> String {
    match self {

      Expression::Symbol(symbol) => {
        symbol.format(formatter)
      },

      Expression::Function(function) => {
        function.format(formatter)
      },

      Expression::Sequence(sequence) => {
        sequence.format(formatter)
      },

      Expression::Variable(variable) => {
        variable.format(formatter)
      },

      Expression::SequenceVariable(variable) => {
        variable.format(formatter)
      },

      Expression::StringLiteral(literal) => {
        literal.format(formatter)
      },

      Expression::Integer(integer) => {
        integer.format(formatter)
      },

      Expression::Real(real) => {
        real.format(formatter)
      },

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

    }
  }
}


impl Hash for Expression {
  fn hash<H: Hasher>(&self, state: &mut H) {
    state.write_u64(self.hash())
  }
}


display_formattable_impl!(Expression);
