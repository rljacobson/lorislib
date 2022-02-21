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

use crate::{
  expression::{
    RcExpression,
    Expression
  },
  attributes::Attributes,
  formatter::{
    Formatable,
    Formatter
  },
  normal_form::NormalFormOrder
};

use super::Atom;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function{
  pub name: String,
  pub children: Vec<RcExpression>,
  pub attributes: Attributes
}


impl Function {

  pub fn new(name: String) -> Function {
    Function{
      name,
      children: Vec::new(),
      attributes: Attributes::default()
    }
  }

  pub fn len(&self)  -> usize {
    self.children.len()
  }

  pub fn part(&self, idx: usize) -> RcExpression {
    self.children[idx].clone()
  }

  pub fn commutative(&self) -> bool {
    self.attributes.commutative()
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


impl Formatable for Function {
  fn format(&self, formatter: &Formatter) -> String {
    format!(
      "{}({})",
      self.name,
      self.children
      .iter()
      .map(|c| c.format(formatter))
      .collect::<Vec<_>>()
      .join(", ")
    )
  }
}

impl NormalFormOrder for Function {
  /// For the purposes of `NormalFormOrder`, two functions are equal if their names are equal.
  fn cmp(&self, other: &Self) -> Ordering {
    // todo: Prohibit distinct expressions with the same name, presumably in the symbol table.
    self.name.cmp(&other.name)
  }
}

impl Atom for Function {
  fn as_expression(self) -> Expression {
    Expression::Function(self)
  }
}

impl From<Function> for Expression {
  fn from(function: Function) -> Self {
    Expression::Function(function)
  }
}


display_formatable_impl!(Function);



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

    let a = Rc::new(Variable("a".into()).as_expression());
    let b = Rc::new(Variable("b".into()).as_expression());
    let c = Rc::new(Variable("c".into()).as_expression());
    let d = Rc::new(Variable("d".into()).as_expression());
    let e = Rc::new(Variable("e".into()).as_expression());
    let h = Rc::new(Variable("h".into()).as_expression());

    let mut g = Function::new("f".into());
    g.attributes.set(Attribute::Associative);
    g.attributes.set(Attribute::Variadic);
    g.children = vec![a.clone(), b.clone(), c.clone(), d.clone(), e.clone(), h.clone()];

    let mut f1 = Function::new("f".into());
    f1.attributes.set(Attribute::Associative);
    f1.attributes.set(Attribute::Variadic);

    f1.children.push(a);

    let mut sequence_inner = Sequence::default();
    sequence_inner.children.push(d);
    sequence_inner.children.push(e);


    let mut f2 = Function::new("f".into());
    f2.attributes.set(Attribute::Associative);
    f2.attributes.set(Attribute::Variadic);

    f2.children.push(b);
    f2.children.push(c);
    f2.children.push(Rc::new(sequence_inner.into()));
    f2.children.push(h);

    let mut sequence_outer = Sequence::default();

    sequence_outer.children.push(Rc::new(f2.into()));
    f1.children.push(Rc::new(sequence_outer.into()));

    println!("{}", f1);
    f1.associative_normal_form();
    println!("{}", f1);

    assert_eq!(f1, g);
  }

  #[test]
  fn formatted_function() {
    let v = Rc::new(Variable("a".into()).as_expression());
    let u = Rc::new(SequenceVariable("b".into()).as_expression());
    let mut f = Function::new("f".into());
    f.children = vec![v, u];
    assert_eq!(f.format(&Formatter::default()), "f(‹a›, «b»)");
  }

  #[test]
  fn function_len() {
    let v = Rc::new(Variable("a".into()).as_expression());
    let u = Rc::new(Variable("b".into()).as_expression());
    let mut f = Function::new("f".into());
    f.children = vec![v, u];
    assert_eq!(f.len(), 2);
  }

  #[test]
  fn function_part() {
    let v = Rc::new(Variable("a".into()).as_expression());
    let u = Rc::new(Variable("b".into()).as_expression());
    let mut f = Function::new("f".into());
    f.children = vec![v, u.clone()];
    assert_eq!(f.part(1), u);
  }

  #[test]
  fn function_normal_form_ordering(){
    let mut f: Function = Function::new("f".into());
    let mut g: Function = Function::new("g".into());

    f.children = vec![
    Rc::new(Variable("a".into()).as_expression()),
    Rc::new(Variable("b".into()).as_expression()),
    Rc::new(Variable("c".into()).as_expression()),
    Rc::new(Variable("d".into()).as_expression()),
    ];
    g.children = f.children.clone();
    g.children.push(Rc::new(Variable("e".into()).as_expression()));

    assert_eq!(NormalFormOrder::cmp(&f, &g), Ordering::Less);
    assert_eq!(NormalFormOrder::cmp(&g, &f), Ordering::Greater);

    g.children = vec![];

    assert_eq!(NormalFormOrder::cmp(&f, &g), Ordering::Less);
    assert_eq!(NormalFormOrder::cmp(&g, &f), Ordering::Greater);

    g.children = f.children.clone();
    f.children.push(Rc::new(Variable("e".into()).as_expression()));

    assert_eq!(NormalFormOrder::cmp(&f, &g), Ordering::Less);
    assert_eq!(NormalFormOrder::cmp(&g, &f), Ordering::Greater);
  }
}
