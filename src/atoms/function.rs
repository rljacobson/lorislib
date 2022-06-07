/*!
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

use std::{
  cmp::Ordering,
  rc::Rc
};
use std::hash::Hasher;
use fnv::FnvHasher;

use crate::{
  expression::{
    RcExpression,
    Expression,
    ExpressionKind
  },
  attributes::Attributes,
  format::{
    Formattable,
    Formatter
  },
  normal_form::NormalFormOrder
};

use super::{Atom, Symbol, Variable};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function{
  /// The head of the function is either a symbol or a variable. It cannot be a
  /// function, sequence, or sequence variable.
  pub cached_hash: u64,
  pub head: RcExpression,
  pub children: Vec<RcExpression>,
  pub attributes: Attributes,
}


impl Function {

  /// Creates a new function having a head that is a symbol of the name `name`.
  pub fn with_symbolic_head(name: &str) -> Function {
    let head = Rc::new(Symbol(name.to_string()).to_expression());
    Function::new(head).unwrap()
  }

  /// Creates a new function having a head that is a variable of the name `name`.
  pub fn with_variable_head(name: &str) -> Function {
    let head = Rc::new(Variable(name.to_string()).to_expression());
    Function::new(head).unwrap()
  }

  /// Creates a new function or function variable. If an expression other than a
  /// symbol or variable is given for the head, an error is return.
  pub fn new(head: RcExpression) -> Result<Function, ()> {
    match (head.as_ref()).into() {

      | ExpressionKind::Symbol
      | ExpressionKind::Variable => {
        Ok(
          Function{
            cached_hash: 0,
            head,
            children: Vec::new(),
            attributes: Attributes::default()
          }
        )
      },

      _ => {
        Err(())
      }

    }
  }

  pub fn duplicate_head(&self) -> Function {
    Function{
      cached_hash: 0,
      head: self.head.clone(),
      children: Vec::new(),
      attributes: self.attributes.clone()
    }
  }


  pub fn duplicate_with_rest(&self) -> Function {
    Function{
      cached_hash: 0,
      head: self.head.clone(),
      children: self.rest(),
      attributes: self.attributes.clone()
    }
  }


  pub fn len(&self)  -> usize {
    self.children.len()
  }

  pub fn part(&self, idx: usize) -> RcExpression {
    self.children[idx].clone()
  }

  pub fn push(&mut self, child: RcExpression) {
    self.children.push(child);
  }

  /// Returns the first child.
  pub fn first(&self) -> Option<RcExpression> {
    if self.children.len() >= 1 {
      Some(self.children[0].clone())
    } else {
      None
    }
  }

  /// Returns a vector containing all but the first child. If there are zero or one children, returns an empty vector.
  pub fn rest(&self) -> Vec<RcExpression> {
    let mut result = Vec::new();
    if self.children.len() > 1 {
      self.children[1..].clone_into(&mut result);
    }
    result
  }

  /// Is the head of this function a function variable?
  pub fn is_function_variable(&self) -> bool {
    ExpressionKind::Variable == self.head.as_ref().into()
  }

  pub fn commutative(&self) -> bool {
    self.attributes.commutative()
  }

  pub fn associative(&self) -> bool {
    self.attributes.associative()
  }

  pub fn free(&self) -> bool {
    !(self.attributes.associative() || self.attributes.commutative())
  }

  /// Rewrites the function into associative normal form by flattening any
  /// nested occurences of the same function.
  pub fn associative_normal_form(&mut self) {
    if !(self.attributes.associative() && self.attributes.variadic()) {
      /*
        It isn't enough to just be associative. Suppose ƒ is a binary associative
        function. Then ƒ(ƒ(a, b), c) = ƒ(a, ƒ(b, c)), but ƒ cannot be flattened
        to ƒ(a, b, c).
      */
      return;
    }

    // Make sure all children are flat.
    for child in self.children.iter_mut() {
      let mut_child: &mut Expression = Rc::<Expression>::make_mut(child);
      mut_child.associative_normal_form();
    }

    /*

      The following code does not completely flatten the function. Consider the
      expression `ƒ(a, (b, ƒ(c)))`. Every child of the outer ƒ is already in
      associative-normal form. The code below will transform the expression as:
      `ƒ(a, (b, ƒ(c)))` -> `ƒ(a, b, ƒ(c))`, which is not in a-normal form.

      Worse, consider: `ƒ(a, (b, ƒ(c, (d, f(e)))))` -> `ƒ(a, b, ƒ(c, d, ƒ(e)))`.
      The solution is to check again if a sequence is spliced. Because the children
      are already in a-normal form, the second loop is guaranteed not to encounter
      a sequence.

    */

    // Initialized to true to allow the first loop.
    let mut found_a_squence: bool = true;

    while found_a_squence {
      found_a_squence = false;

      let mut child_stack: Vec<(usize, RcExpression)> = vec![];
      let mut additional_children: usize = 0;
      for (i, child) in self.children.iter().enumerate() {
        // Variadic associative functions flatten two kinds of children: functions
        // of the same name, and any and all sequences.
        match &**child {

          Expression::Function(function) if self.is_equal(function) => {
              additional_children += function.len() - 1;
              child_stack.push((i, child.clone()));
            },

          Expression::Sequence(sequence) => {
            additional_children += sequence.len() - 1;
            child_stack.push((i, child.clone()));
            found_a_squence = true;
          },

          _ => continue

        }
      }

      self.children.reserve_exact(additional_children);
      // Iterating over the stack in reverse maintains the validity of the index `i`.
      for (i, child) in child_stack.iter().rev(){
        // Destructure
        match &**child {

          Expression::Function(function) => {
            self.children.splice(i..=i, function.children.iter().map(|e| e.clone()));
          }

          Expression::Sequence(sequence) => {
            self.children.splice(i..=i, sequence.children.iter().map(|e| e.clone()));
          },

          _ => {
            unreachable!()
          }

        } // end match on child
      } // end stack processing loop

    } // end for repeat
  }

  /// Rewrites the sequence into commutative normal form by sorting the children
  /// according to `NormalFormOrder`.
  pub fn commutative_normal_form(&mut self) {

    // Put all children in commutative normal form.
    for child in self.children.iter_mut() {
      let mut_child: &mut Expression = Rc::<Expression>::make_mut(child);
      mut_child.commutative_normal_form();
    }

    // Now put `self` into commutative normal form.
    self.children.sort_unstable_by(|x, y| Expression::cmp(x, y) );
  }

}


impl Formattable for Function {
  fn format(&self, formatter: &Formatter) -> String {
    format!(
      // "{}({})",
      "{}❨{}❩",
      self.head,
      self.children
      .iter()
      .map(|c| c.format(formatter))
      .collect::<Vec<_>>()
      .join(", ")
    )
  }
}

impl NormalFormOrder for Function {
  /// Two functions are equal if their names are equal, if their lengths are equal, and if their
  /// corresponding children are equal.
  fn cmp(&self, other: &Self) -> Ordering {
    // todo: Prohibit distinct expressions with the same name, presumably in the symbol table.
    self.head.cmp(&other.head)
  }
}

impl Atom for Function {

  fn hash(&mut self) -> u64 {
    if self.cached_hash != 0 {
      return self.cached_hash;
    }

    let mut hasher = FnvHasher::default();

    hasher.write(&[72u8, 5u8, 244u8, 86u8, 5u8, 210u8, 69u8, 30u8]);
    for part in self.children {
      hasher.write_u64(part.hash());
    }

    let result       = hasher.finish();
    self.cached_hash = result;

    result
  }

  fn to_expression(self) -> Expression {
    Expression::Function(self)
  }
}

impl From<Function> for Expression {
  fn from(function: Function) -> Self {
    Expression::Function(function)
  }
}


display_formattable_impl!(Function);



#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use super::*;
  use crate::{
    atoms::{
      Variable,
      SequenceVariable,
      Sequence
    },
    attributes::Attribute
  };

  #[test]
  fn a_normal_form() {
    // If this test is modified, be sure the modified version still tests
    // a mutually nested case similar to `ƒ(a, (b, ƒ(c)))`. (See the
    // comment in `Self::associative_normal_form()`.)

    let a = Rc::new(Variable("a".into()).to_expression());
    let b = Rc::new(Variable("b".into()).to_expression());
    let c = Rc::new(Variable("c".into()).to_expression());
    let d = Rc::new(Variable("d".into()).to_expression());
    let e = Rc::new(Variable("e".into()).to_expression());
    let h = Rc::new(Variable("h".into()).to_expression());

    let mut g = Function::with_symbolic_head("f");
    g.attributes.set(Attribute::Associative);
    g.attributes.set(Attribute::Variadic);
    g.children = vec![a.clone(), b.clone(), c.clone(), d.clone(), e.clone(), h.clone()];

    let mut f1 = Function::with_symbolic_head("f");
    f1.attributes.set(Attribute::Associative);
    f1.attributes.set(Attribute::Variadic);

    f1.children.push(a);

    let mut sequence_inner = Sequence::default();
    sequence_inner.children.push(d);
    sequence_inner.children.push(e);


    let mut f2 = Function::with_symbolic_head("f");
    f2.attributes.set(Attribute::Associative);
    f2.attributes.set(Attribute::Variadic);

    f2.children.push(b);
    f2.children.push(c);
    f2.children.push(Rc::new(sequence_inner.into()));
    f2.children.push(h);

    let mut sequence_outer = Sequence::default();

    sequence_outer.children.push(Rc::new(f2.into()));
    f1.children.push(Rc::new(sequence_outer.into()));

    // println!("{}", f1);
    f1.associative_normal_form();
    // println!("{}", f1);

    assert_eq!(f1, g);
  }

  #[test]
  fn formatted_function() {
    let v = Rc::new(Variable("a".into()).to_expression());
    let u = Rc::new(SequenceVariable("b".into()).to_expression());
    let mut f = Function::with_symbolic_head("f");
    f.children = vec![v, u];
    // assert_eq!(f.format(&Formatter::default()), "f(‹a›, «b»)");
    assert_eq!(f.format(&Formatter::default()), "f❨‹a›, «b»❩");
  }

  #[test]
  fn function_len() {
    let v = Rc::new(Variable("a".into()).to_expression());
    let u = Rc::new(Variable("b".into()).to_expression());
    let mut f = Function::with_symbolic_head("f");
    f.children = vec![v, u];
    assert_eq!(f.len(), 2);
  }

  #[test]
  fn function_part() {
    let v = Rc::new(Variable("a".into()).to_expression());
    let u = Rc::new(Variable("b".into()).to_expression());
    let mut f = Function::with_symbolic_head("f");
    f.children = vec![v, u.clone()];
    assert_eq!(f.part(1), u);
  }

  #[test]
  fn function_normal_form_ordering(){
    let mut f: Function = Function::with_symbolic_head("f");
    let mut g: Function = Function::with_symbolic_head("g");

    f.children = vec![
      Rc::new(Variable("a".into()).to_expression()),
      Rc::new(Variable("b".into()).to_expression()),
      Rc::new(Variable("c".into()).to_expression()),
      Rc::new(Variable("d".into()).to_expression()),
    ];
    g.children = f.children.clone();
    g.children.push(Rc::new(Variable("e".into()).to_expression()));

    assert_eq!(NormalFormOrder::cmp(&f, &g), Ordering::Less);
    assert_eq!(NormalFormOrder::cmp(&g, &f), Ordering::Greater);

    g.children = vec![];

    assert_eq!(NormalFormOrder::cmp(&f, &g), Ordering::Less);
    assert_eq!(NormalFormOrder::cmp(&g, &f), Ordering::Greater);

    g.children = f.children.clone();
    f.children.push(Rc::new(Variable("e".into()).to_expression()));

    assert_eq!(NormalFormOrder::cmp(&f, &g), Ordering::Less);
    assert_eq!(NormalFormOrder::cmp(&g, &f), Ordering::Greater);
  }
}
