/*!

Primitive expression node types.

*/

use std::{
  rc::Rc,
  cmp::Ordering
};
use std::hash::{Hash, Hasher};

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
    InternedString,
    resolve_str,
    interned_static
  },
  format::{
    Formattable,
    ExpressionFormatter,
    display_formattable_impl
  },
  normal_form::NormalFormOrder,
};
use crate::format::DisplayForm;

#[derive(Clone, PartialEq, Debug, IntoStaticStr, EnumDiscriminants)]
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

  /// Reports the `AtomKind` of `self`.
  pub fn kind(&self) -> AtomKind {
    self.into()
  }

  /// Reports the `AtomKind` of the head.
  pub fn head_kind(&self) -> AtomKind {
    match self {
      Atom::SExpression(children) => {
        children[0].kind()
      }

      atom => {
        // The head of any non-function is a symbol.
        AtomKind::Symbol
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

      Atom::SExpression(children) => children.len() - 1 // Don't count the head.
    }
  }

  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  // region Pattern Matching Utilities

  /// Is `atom` the symbol `True`
  pub fn is_true(&self) -> bool {
    *self == Atom::Symbol(interned_static("True"))
  }

  /// If `self` has the form `Sequence[a, b, …]`, returns a vector of only the children `a, b, …`.
  pub fn is_sequence(&self) -> Option<Vec<Atom>> {
    if let Atom::SExpression(children) = self {
      if children[0] == Symbol::from_static_str("Sequence"){
        return Some(children[1..].to_vec());
      }
    }
    None
  }

  pub(crate) fn is_function_variable(&self) -> Option<InternedString> {
    match self {
      Atom::SExpression(children) => {
        children[0].is_variable()
      }
      _ => None
    }
  }

  pub(crate) fn is_any_variable_kind(&self) -> bool {
    self.check_variable_pattern("Blank").is_some()
        || self.check_variable_pattern("BlankSequence").is_some()
        || self.check_variable_pattern("BlankNullSequence").is_some()
  }

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


impl Eq for Atom {}

/**
  If two expressions just happen to have the same representation, a string and a symbol, we still want their hashes
  to differ. So we hash a type-specific prefix before hashing the data. We use the same prefix as Cory's expreduce
  for compatibility. Some of the atoms in expreduce don't exist in loris, and some of our atoms don't exist in
  expreduce. I believe Cory chose his prefixes at random. We do the same.

  expreduce

      real      : [195, 244, 76 , 249, 227, 115, 88 , 251]
      complex   : [82 , 226, 223, 39 , 113, 26 , 149, 249]
      expression: [72 , 5  , 244, 86 , 5  , 210, 69 , 30]
      integer   : [242, 99 , 84 , 113, 102, 46 , 118, 94]
      rational  : [90 , 82 , 214, 51 , 52 , 7  , 7  , 33]
      string    : [102, 206, 57 , 172, 207, 100, 198, 133]
      symbol    : [107, 10 , 247, 23 , 33 , 221, 163, 156]

  Loris


    real      : [195, 244, 76 , 249, 227, 115, 88 , 251]
  s-expression: [72 , 5  , 244, 86 , 5  , 210, 69 , 30]
    integer   : [242, 99 , 84 , 113, 102, 46 , 118, 94]
    string    : [102, 206, 57 , 172, 207, 100, 198, 133]
    symbol    : [107, 10 , 247, 23 , 33 , 221, 163, 156]

*/
impl Hash for Atom {
  fn hash<H: Hasher>(&self, hasher: &mut H) {
    match self {
      Atom::String(v) => {
        hasher.write(&[102, 206, 57 , 172, 207, 100, 198, 133]);
        v.hash(hasher);
      }

      Atom::Integer(v) => {
        hasher.write(&[242, 99, 84, 113, 102, 46, 118, 94]);
        v.hash(hasher)
      }

      Atom::Real(v) => {
        hasher.write(&[195, 244, 76 , 249, 227, 115, 88 , 251]);
        v.as_raw().hash(hasher);
      }

      Atom::Symbol(v) => {
        hasher.write(&[107, 10 , 247, 23 , 33 , 221, 163, 156]);
        v.hash(hasher);
      }

      Atom::SExpression(v) => {
        hasher.write(&[72 , 5  , 244, 86 , 5  , 210, 69 , 30]);
        for part in v.as_ref() {
          part.hash(hasher);
        }
      }

    }
  }
}

impl Formattable for Atom {
  fn format(&self, formatter: &ExpressionFormatter) -> String {
    match self {
      Atom::String(v) => {
        format!("\"{}\"", resolve_str(*v))
      }
      Atom::Integer(v) => {
        format!("{}", v)
      }
      Atom::Real(v) => {
        format!("{}", v)
      }
      Atom::Symbol(v) => {
        format!("{}", resolve_str(*v))
      }
      Atom::SExpression(v) => {
        if let Some(name) = self.is_variable() {
          match formatter.form {
            DisplayForm::Matcher => {
              format!("‹{}›", resolve_str(name))
            }
            _ => {
              format!("{}_", resolve_str(name))
            }
          }
        } else if let Some(name) = self.is_sequence_variable() {
          // todo: distinguish sequence variables from null sequence variables
          match formatter.form {
            DisplayForm::Matcher => {
              format!("«{}»", resolve_str(name))
            }
            _ => {
              format!("{}__", resolve_str(name))
            }
          }
        } else if let Some(name) = self.is_null_sequence_variable() {
          match formatter.form {
            DisplayForm::Matcher => {
              format!("«{}»", resolve_str(name))
            }
            _ => {
              format!("{}___", resolve_str(name))
            }
          }
        } else {
          // A "normal" function
          match formatter.form {

            DisplayForm::Matcher => {
              let mut child_iter = v.iter();
              let head = child_iter.next().unwrap();
              format!(
                // "{}({})",
                "{}❨{}❩",
                // "{}[{}]",
                head,
                child_iter.map(|c| c.format(formatter))
                          .collect::<Vec<_>>()
                          .join(", ")
              )
            }

            _ => {
              let mut child_iter = v.iter();
              let head = child_iter.next().unwrap();
              format!(
                // "{}({})",
                // "{}❨{}❩",
                "{}[{}]",
                head,
                child_iter.map(|c| c.format(formatter))
                          .collect::<Vec<_>>()
                          .join(", ")
              )
            }
          }

        }
      }
    }
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
        for (left, right) in f.iter().zip(g.iter()) {
          let ordering: Ordering = NormalFormOrder::cmp(left, right);
          if ordering == Ordering::Less {
            return Ordering::Less;
          } else if ordering == Ordering::Greater {
            return Ordering::Greater;
          }
        };
        // If we get this far, expression pairs have been equal. Compare lengths.
        f.len().cmp(&g.len())
      },

      (Atom::Integer(v), Atom::Integer(u))
      => {
        // Value comparison. Note that comparing an `Atom::Integer` and a `Atom::Real` does NOT use value comparison.
        v.cmp(u)
      },

      (Atom::Real(s), Atom::Real(t))
      => {
        // Value comparison. Note that comparing an `Atom::Integer` and a `Atom::Real` does NOT use value comparison.
        match s.partial_cmp(t) {
          Some(ordering) => ordering,
          None => {
            unsafe {
              (*s.as_raw()).d.cmp(&(*t.as_raw()).d)
            }
          }
        }
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
#[allow(non_snake_case)]
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

#[allow(non_snake_case)]
pub(crate) mod SExpression {
  use std::rc::Rc;
  use super::*;
  use crate::interner::{
    InternedString
  };

  // region Convenience construction functions
  // Using these functions decreases the probability of an incorrectly constructed expression.

  /// Creates a new `Atom::SExpression` having head  `head` and children `children`.
  pub(crate) fn new(head: Atom, mut children: Vec<Atom>) -> Atom {
    let mut new_children = Vec::with_capacity(children.len()+1);
    new_children.push(head);
    new_children.append(&mut children);
    Atom::SExpression(Rc::new(new_children))
  }

  /// We often have a need to create an expression for some standard built-in or stdlib symbol.
  pub(crate) fn with_str_head(head_str: &'static str) -> Atom {
    Atom::SExpression(Rc::new(vec![Symbol::from_static_str(head_str)]))
  }

  /// We often have a need to create an expression for some standard built-in or stdlib symbol.
  pub(crate) fn with_symbolic_head(head: InternedString) -> Atom {
    Atom::SExpression(Rc::new(vec![Atom::Symbol(head)]))
  }

  /// Creates an empty `Sequence[]`.
  pub(crate) fn empty_sequence() -> Atom {
    Atom::SExpression(Rc::new(vec![Symbol::from_static_str("Sequence")]))
  }

  /// Creates a `Sequence[]` with the provided children.
  pub(crate) fn sequence(mut children: Vec<Atom>) -> Atom {
    let mut new_children = Vec::with_capacity(children.len()+1);
    new_children.push(Symbol::from_static_str("Sequence"));
    new_children.append(&mut children);
    Atom::SExpression(Rc::new(new_children))
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
  pub(crate) fn children(function: &Atom) -> Rc<Vec<Atom>> {
    if let Atom::SExpression(children) = function {
      children.clone()
    } else {
      unreachable!("Tried to `SExpression::destructure` a non-S-expression `Atom`.");
    }
  }


  /// Makes a copy of `function` with the same head and no (other) children.
  /// Panics if you provide anything other than `Atom::SExpression`.
  pub(crate) fn duplicate_with_head(function: &Atom) -> Atom {
    let children = children(function);
    let new_children = vec![children[0].clone()];

    Atom::SExpression(Rc::new(new_children))
  }

  /// Makes a copy of `function` with the same head and with all the children except for the first one (`children[1]`).
  /// In other words, it makes a clone of the first function and drops the child at index 1.
  /// Panics if you provide anything other than `Atom::SExpression`.
  pub(crate) fn duplicate_with_rest(function: &Atom) -> Atom {
    let children = children(function);
    let mut child_iter = children.iter();
    let mut new_children = Vec::with_capacity(children.len());
    // Clone the head.
    new_children.push(child_iter.next().unwrap().clone());
    // Skip the first child.
    child_iter.next();
    new_children.extend(child_iter.cloned());

    Atom::SExpression(Rc::new(new_children))
  }

  /// Return the expression at index `n` in the S-expression. Indices start at 0, and the 0th element is
  /// always the head of the expression. This function panics if expression isn't an S-expression. For
  /// the behavior of `Part[exp, n]`, use the built-in.
  pub(crate) fn part(expression: &Atom, n: usize) -> Atom {
    let children = children(expression);
    children[n].clone()
  }

  /// Creates a new S-expression with the same children as `children` except that
  /// `children[0]` is `head`. Each child is cloned.
  pub(crate) fn new_swapped_head(head: Atom, children: &Vec<Atom>) -> Atom {
    let mut new_children = Vec::with_capacity(children.len()+1);
    new_children.push(head);
    new_children.extend(children[1..].iter().cloned());
    Atom::SExpression(Rc::new(new_children))
  }

  /// If the head is a variable, returns the name of the variable.
  pub(crate) fn is_head_variable(expression: &Atom) -> Option<InternedString> {
    match expression {

      Atom::SExpression(children) => {
        children[0].is_variable()
      }

      _ => None

    }
  }

}
