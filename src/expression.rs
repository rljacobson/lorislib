/*!

An expression is a syntatically correct "thing", a symbol, function, sequence,
non-sequence variable, or sequence variable. We try to keep `Expression`s
immutable. We can use `Rc<Expression>`, aliased to `RcExpression`, as a garbage
collected copy-on-write smart pointer.

To implement matching on your own structures, implement a `get_expression`
method or equivalent that returns the expression form of the type. Match on
the expression, and transform the result back into your native types.

*/

use std::{rc::Rc, cmp::Ordering};

use strum::{EnumDiscriminants, Display};
use lazy_static::lazy_static;

use crate::{
  formatter::{
    Formatable,
    Formatter
  },
  atoms::{
    Symbol,
    Function,
    Variable,
    Sequence,
    SequenceVariable
  },
  normal_form::NormalFormOrder
};


pub type RcExpression = Rc<Expression>;

#[derive(Clone, PartialEq, Eq, EnumDiscriminants, Debug, Hash)]
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
  parentheses are dropped.

  The children of a function are an ordered list (a `Vec<RcExpression>`) of
  expressions even when the function is commutative. The attributes of a
  function record whether it is commutative or associative and potentially
  other boolean data about the function.
  */
  Function(Function),

  /**
  A `Sequence` is an ordered list of expressions that can be spliced into a
  functions arguments or into another sequence. For clarity, `Sequence`s will
  always be written with parentheses, even if the sequence is empty: `()`, `(a,
  f(b), c)`, etc. A `Sequence` is amcontiguous sublist of terms from a possiblely
  larger list that we want to call out specifically for some purpose.
  */
  Sequence(Sequence),

  /// A `Variable` is a placeholder for an atom and may be bound or unbound.
  Variable(Variable),

  /// A sequence variable is a placeholder for a sequence, that is, a variable that
  /// only holds sequences.
  SequenceVariable(SequenceVariable),

}

lazy_static!{
  static ref EMPTY_STRING: String = String::from("");
}
// static EMPTY_STRING: String = String::from("");

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

          _ => unreachable!()

        }
      },
      Expression::Sequence(_) => &EMPTY_STRING,
      Expression::SequenceVariable(SequenceVariable(name)) => &name,
      Expression::Symbol(Symbol(name)) => &name,
      Expression::Variable(Variable(name)) => &name,
    }
  }

  pub fn len(&self) -> usize {
    match self {

      // todo: Should non M-expressions have a positive length?
      | Expression::Symbol(_)
      | Expression::Variable(_)
      | Expression::SequenceVariable(_) => 1,

      Expression::Function(function) => function.len(),

      Expression::Sequence(sequence) => sequence.len(),

    }
  }

  pub fn associative_normal_form(&mut self) {
    match self {

        Expression::Function(function) => function.associative_normal_form(),

        Expression::Sequence(sequence) => sequence.associative_normal_form(),

        _ => { /* nothing to do */ }
    }
  }


  pub fn commutative_normal_form(&mut self) {
    match self {

        Expression::Function(function) => function.commutative_normal_form(),

        Expression::Sequence(sequence) => sequence.commutative_normal_form(),

        _ => { /* nothing to do */ }
    }
  }


  pub fn normal_form(&mut self) {
    self.associative_normal_form();
    self.commutative_normal_form();
  }
}


impl Formatable for Expression {
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
      }

    }
  }
}


impl NormalFormOrder for Expression {
  fn cmp(&self, other: &Self) -> Ordering {
    match (self, other) {

      // Same expression type //

      (Expression::Symbol(s), Expression::Symbol(t))
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


display_formatable_impl!(Expression);
