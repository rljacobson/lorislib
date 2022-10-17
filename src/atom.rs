/*!

Primitive expression node types.

 */

use std::{
  fmt::{Display, Formatter},
  rc::Rc,
  cmp::Ordering
};

use strum_macros::{
  EnumDiscriminants,
  IntoStaticStr
};
use rug::{
  Integer as BigInteger,
  Float as BigFloat,
};


use crate::{
  interner::{
    interned_static,
    InternedString,
    resolve_str
  },
  format::{
    Formattable,
    ExpressionFormatter
  },
  normal_form::NormalFormOrder
};
use crate::atom::SExpression::destructure;

#[derive(Clone, PartialEq, Eq, IntoStaticStr, EnumDiscriminants)]
#[strum_discriminants(name(AtomKind))]
pub enum Atom {
  String(InternedString),
  Integer(BigInteger),
  Real(BigFloat),
  Symbol(InternedString),
  SExpression(Rc<Vec<Atom>>)
}

impl Atom {
  pub fn head(&self) -> Atom {
    match self {
      Atom::SExpression(children) => {
        match children.first() {
          Some(expression) => expression.clone(),
          None => headless_s_expression(),
        }
      }

      atom => {
        Symbol::from_static_str(atom.into())
      }
    }
  }

  /// Gives the symbol (as an `InternedString`) under which the properties of this
  /// expression would be stored in the symbol table.
  pub fn name(&self) -> Option<InternedString> {
    match self {
      Atom::SExpression(_) => {
        match self.head() {
          Atom::Symbol(name) => Some(name),
          _                  => None
        }
      },
      Atom::Symbol(name) => Some(*name),
      _                  => None
    }
  }

  // todo: Should the return type be the machine sized index type (usize)?
  /// Returns the length of the expression. Only S-Expressions can have nonzero length.
  /// For string length, use the `StringLength` function (currently unimplemented).
  pub fn len(&self) -> usize {
    match self {
      | Atom::String(_)
      | Atom::Integer(_)
      | Atom::Real(_)
      | Atom::Symbol(_) => 0,

      Atom::SExpression(children) => children.len()
    }
  }

  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  // region Pattern Matching Utilities

  /// Checks if `self` has the form `Pattern[□, Blank[□]]` (equiv. `□_□`).
  /// Returns the name if `self` is a `Blank`.
  pub fn is_variable(&self) -> Option<InternedString> {
    self.check_variable_pattern("Blank")
  }

  /// Checks if `self` has the form `Pattern[□, BlankSequence[□]]` (equiv. `□__□`).
  /// Returns the name if `self` is a `BlankSequence`.
  pub fn is_sequence_variable(&self) -> Option<InternedString> {
    self.check_variable_pattern("BlankSequence")
  }

  /// Checks if `self` has the form `Pattern[□, BlankNullSequence[□]]` (equiv. `□___□`).
  /// Returns the name if `self` is a `BlankNullSequence`.
  pub fn is_null_sequence_variable(&self) -> Option<InternedString> {
    self.check_variable_pattern("BlankNullSequence")
  }

  /// Auxiliary function for `is_*_variable` functions. (Do not use for validation.)
  fn check_variable_pattern(&self, symbol: &'static str) -> Option<InternedString> {
    if let Atom::SExpression(children) = self {
      if children.len() > 2
          && children[0] == Symbol::from_static_str("Pattern")
          && children[2].head() == Symbol::from_static_str(symbol)
      {
        return children[1].name();
      }
    }
    None
  }

  pub fn is_number(&self) -> bool {
    match self {
      Atom::Integer(_)
      | Atom::Real(_) => true,
      _ => false,
    }
  }

  // endregion
}

impl Formattable for Atom {
  fn format(&self, formatter: &ExpressionFormatter) -> String {
    todo!()
  }
}

display_formattable_impl!(Atom);


impl NormalFormOrder for Atom {
  fn cmp(&self, other: &Self) -> Ordering {
    match (self, other) {

      // Same expression type //

      (Atom::Symbol(s), Atom::Symbol(t))
      => std::cmp::Ord::cmp(resolve_str(*s), resolve_str(*t)),

      (Atom::String(s), Atom::String(t))
      => std::cmp::Ord::cmp(resolve_str(*s), resolve_str(*t)),

      (Atom::SExpression(f), Atom::SExpression(g))
      => {
        // S-expressions are compared via lexicographic comparison of their children.
        // Conveniently, Vec implements lexicographic ordering automatically!
        std::cmp::Ord::cmp(f, g)
      },

      (Atom::Integer(v), Atom::Integer(u))
      => {
        // Value comparison. Note that comparing an `Atom::Integer` and a `Atom::Real` does NOT use value comparison.
        v.cmp(u)
      },

      (Atom::Real(s), Atom::Real(t))
      => {
        // Value comparison. Note that comparing an `Atom::Integer` and a `Atom::Real` does NOT use value comparison.
        s.cmp(t)
      },


      // Different expression types //
      // String < Integer < Real < Symbol < SExpression
      (thing_one, thing_two) => {
        if Into::<AtomKind>::into(thing_one) as u32
            > Into::<AtomKind>::into(thing_two) as u32
        {
          Ordering::Greater
        } else {
          Ordering::Less
        }

      } // end match branch (thing_one, thing_two)

    } // end match
  }
}

/// A critical error state.
fn headless_s_expression() -> ! {
  unreachable!("Encountered an S-expression without a head, which is impossible. This is a bug.")
}


/// There are a variety of common tasks that apply only to a specific variant of `Atom`. Instead of packing them all
/// into `Atom`'s impl, we put them into free functions in a module named after the variant. The functions that remain
/// in `Atom`'s impl are those that could reasonably be called on any `Atom` variant.

pub(crate) mod Symbol {
  use crate::atom::Atom;
  use crate::interner::{
    interned,
    interned_static
  };

  /// We often have a need to create an expression for some standard built-in or stdlib symbol.
  pub(crate) fn from_static_str(name: &'static str) -> Atom {
    Atom::Symbol(interned_static(name))
  }

  /// Create a symbol from a `&str`.
  pub(crate) fn from_str(name: &str) -> Atom {
    Atom::Symbol(interned(name))
  }

}


pub(crate) mod SExpression {
  use std::rc::Rc;
  use super::*;
  use crate::interner::{
    interned_static,
    InternedString
  };

  // region Convenience construction functions

  /// We often have a need to create an expression for some standard built-in or stdlib symbol.
  pub(crate) fn with_str_head(head_str: &'static str) -> Atom {
    Atom::SExpression(Rc::new(vec![Symbol::from_static_str(head_str)]))
  }

  /// We often have a need to create an expression for some standard built-in or stdlib symbol.
  pub(crate) fn with_symbolic_head(head: InternedString) -> Atom {
    Atom::SExpression(Rc::new(vec![Atom::Symbol(head)]))
  }
  
  /// Creates a sequence variable, i.e. an expression of the form `Pattern[name, BlankSequence[]]`. The provided
  /// `name` is turned into a symbol.
  pub(crate) fn null_sequence_variable(name: &'static str) -> Atom {
    make_variable(name, "BlankNullSequence")
  }
  
  /// Creates a sequence variable, i.e. an expression of the form `Pattern[name, BlankSequence[]]`. The provided
  /// `name` is turned into a symbol.
  pub(crate) fn sequence_variable(name: &'static str) -> Atom {
    make_variable(name, "BlankSequence")
  }
  
  /// Creates a sequence variable, i.e. an expression of the form `Pattern[name, BlankSequence[]]`. The provided
  /// `name` is turned into a symbol.
  pub(crate) fn variable(name: &'static str) -> Atom {
    make_variable(name, "Blank")
  }
  
  /// Creates a sequence variable, i.e. an expression of the form `Pattern[name, BlankSequence[]]`. The provided
  /// `name` is turned into a symbol.
  fn make_variable(name: &'static str, var_kind: &'static str) -> Atom {
    Atom::SExpression(
      Rc::new(
        vec![
          Symbol::from_static_str("Pattern"),
          Symbol::from_static_str(name),
          with_str_head(var_kind)
        ]
      )
    )
  }

  // endregion

  /// An S-expression just wraps a vector. We have to destructure in almost every operation on
  /// S-expressions. This function panics if `expression` is not an `Atom::SExpression`.
  pub(crate) fn destructure(function: Atom) -> Rc<Vec<Atom>> {
    if let Atom::SExpression(children) = function {
      children.clone()
    } else {
      unreachable!("Tried to `SExpression::destructure` a non-S-expression `Atom`.");
    }
  }


  /// Makes a copy of `function` with the same head and no (other) children.
  /// Panics if you provide anything other than `Atom::SExpression`.
  pub(crate) fn duplicate_with_head(&function: Atom) -> Atom {
    let children = destructure(function);
    let new_children = vec![children[0].clone()];

    Atom::SExpression(Rc::new(new_children))
  }

  /// Makes a copy of `function` with the same head and with all the children except for the first one (`children[1]`).
  /// In other words, it makes a clone of the first function and drops the child at index 1.
  /// Panics if you provide anything other than `Atom::SExpression`.
  pub(crate) fn duplicate_with_rest(&function: Atom) -> Atom {
    let children = destructure(function);
    let mut child_iter = children.iter();
    // Clone the head.
    let mut new_children = vec![child_iter.next().unwrap().clone()];
    // Skip the first true child.
    child_iter.next();
    new_children.extend(child_iter.cloned());

    Atom::SExpression(Rc::new(new_children))
  }

  /// Return the expression at index `n` in the S-expression. Indices start at 0, and the 0th element is
  /// always the head of the expression. This function panics if expression isn't an S-expression. For
  /// the behavior of `Part[exp, n]`, use the built-in.
  pub(crate) fn part(expression: Atom, n: usize) -> Atom {
    let children = destructure(expression);
    children[n].clone()
  }
  
  pub(crate) fn push(function: Atom, child: Atom) {
    let children = destructure(function);
    children.as_ref().push(child)
  }
  
}

#[cfg(test)]
mod tests {
  #[test]
  fn it_works() {
    assert_eq!(2 + 2, 4);
  }
}
