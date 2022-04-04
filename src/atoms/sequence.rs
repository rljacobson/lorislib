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
  iter::zip,
  rc::Rc
};

use lazy_static::__Deref;

use crate::{
  expression::{
    RcExpression,
    Expression
  },
  format::{
    Formatable,
    Formatter
  },
  normal_form::NormalFormOrder
};

use super::Atom;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sequence{
  pub children: Vec<RcExpression>,
}


impl Sequence {

  pub fn new() -> Self {
    Self::default()
  }

  pub fn from_children(children: Vec<RcExpression>) -> Self {
    Sequence{
      children
    }
  }

  pub fn push(&mut self, child: RcExpression) {
    self.children.push(child);
  }

  pub fn len(&self)  -> usize {
    self.children.len()
  }

  pub fn part(&self, idx: usize) -> RcExpression {
    self.children[idx].clone()
  }

  /// Collapses any child sequences into `self` without recursing first.
  ///
  /// This is the operation that is common to both `flatten()` and
  /// `associative_normal_form()`.
  fn splice_children(&mut self) {
    let mut child_sequence_stack: Vec<(usize, RcExpression)> = vec![];
    let mut additional_children: usize = 0;
    for (i, child) in self.children.iter().enumerate() {
      if let Expression::Sequence(sequence) = &**child {
        additional_children += sequence.len() - 1;
        child_sequence_stack.push((i, child.clone()));
      }
    }

    self.children.reserve_exact(additional_children);
    // Iterating over the stack in reverse maintains the validity of the index `i`.
    for (i, child) in child_sequence_stack.iter().rev(){
      // Destructure
      if let Expression::Sequence(sequence) = &**child {
        self.children.splice(i..=i, sequence.children.iter().map(|e| e.clone()));
      }
    }

  }

  /// Flattens child sequences, then splices child sequences into `self`.
  ///
  /// This differs from `associative_normal_form()` in that it only flattens
  /// sequences. No method is called on any other child expression besides
  /// sequences.
  pub fn flatten(&mut self) {
    // Flatten all child sequences.
    // This is ugly.
    for child in self.children.iter_mut() {
      if let Expression::Sequence(_) = (*child).deref(){
        let mut_child: &mut Expression = Rc::<Expression>::make_mut(child);
        // We use two if-lets to avoid calling `make_mut` on a child that will
        // never be mutated and potentially making an unnecessary clone.
        if let Expression::Sequence(sequence) = mut_child {
          sequence.flatten();
        }
      }
    }

    self.splice_children();
  }

  /// Rewrites the sequence into associative normal form by first making each
  /// child into A-normal form and then splicing any child sequences into `self`.
  pub fn associative_normal_form(&mut self) {
    // Make sure all children are in A-normal form.
    for child in self.children.iter_mut() {
      let mut_child: &mut Expression = Rc::<Expression>::make_mut(child);
      mut_child.associative_normal_form();
    }

    self.splice_children();
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


impl Default for Sequence {
  fn default() -> Self {
    Sequence{ children: vec![] }
  }
}


impl Formatable for Sequence {
  fn format(&self, formatter: &Formatter) -> String {
    // todo: Should we display the parens if there is only one child?
    if self.children.len() == 1 {
      self.children[0].format(formatter)
    } else {
      format!(
        "({})",
        // "（{}）",
        // "❨{}❩",
        self.children
        .iter()
        .map(|c| c.format(formatter))
        .collect::<Vec<_>>()
        .join(", ")
      )
    }
  }
}

impl NormalFormOrder for Sequence {
  fn cmp(&self, other: &Self) -> Ordering {
    // todo: Prohibit distinct expressions with the same name, presumably in the symbol table.

    let mut order: std::cmp::Ordering = std::cmp::Ordering::Equal;

    for (thing_one, thing_two) in zip(self.children.iter(), other.children.iter()) {
      order = thing_one.cmp(&(*thing_two));
      if order != Ordering::Equal {
        return order;
      }
    }

    if self.len() < other.len() {
      return Ordering::Less;
    } else if self.len() > other.len() {
      return Ordering::Greater;
    }

    order
  }
}

impl Atom for Sequence {
  fn to_expression(self) -> Expression {
    Expression::Sequence(self)
  }
}


impl From<Sequence> for Expression {
  fn from(sequence: Sequence) -> Self {
    Expression::Sequence(sequence)
  }
}


display_formatable_impl!(Sequence);



#[cfg(test)]
mod tests {
  use std::rc::Rc;
  use super::*;
  use crate::atoms::{Variable, SequenceVariable};

  #[test]
  fn formatted_function() {
    let v = Rc::new(Variable("a".into()).to_expression());
    let u = Rc::new(SequenceVariable("b".into()).to_expression());
    let mut f = Sequence::new();
    f.children = vec![v, u];
    assert_eq!(f.format(&Formatter::default()), "(‹a›, «b»)");
  }

  #[test]
  fn function_len() {
    let v = Rc::new(Variable("a".into()).to_expression());
    let u = Rc::new(Variable("b".into()).to_expression());
    let mut f = Sequence::new();
    f.children = vec![v, u];
    assert_eq!(f.len(), 2);
  }

  #[test]
  fn function_part() {
    let v = Rc::new(Variable("a".into()).to_expression());
    let u = Rc::new(Variable("b".into()).to_expression());
    let mut f = Sequence::new();
    f.children = vec![v, u.clone()];
    assert_eq!(f.part(1), u);
  }

  #[test]
  fn function_normal_form_ordering(){
    let mut f: Sequence = Sequence::new();
    let mut g: Sequence = Sequence::new();

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

    assert_eq!(NormalFormOrder::cmp(&g, &f), Ordering::Less);
    assert_eq!(NormalFormOrder::cmp(&f, &g), Ordering::Greater);

    g.children = f.children.clone();
    f.children.push(Rc::new(Variable("e".into()).to_expression()));

    assert_eq!(NormalFormOrder::cmp(&g, &f), Ordering::Less);
    assert_eq!(NormalFormOrder::cmp(&f, &g), Ordering::Greater);
  }
}
