/*!

Integer primitive type. Since this is just a proof of concept, integers are represented by `i64`s.

Todo: Use Rug for arbitrary precision.

*/

use std::{
  cmp::Ordering,
  hash::Hasher,
  convert::From,
};
use fnv::FnvHasher;

use crate::{format::{
  Formattable,
  Formatter
}, normal_form::NormalFormOrder, expression::Expression};
use crate::atoms::unwrap_atom_impl;

use super::Atom;


#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct Integer(pub i64);

unwrap_atom_impl!(Integer);

impl Formattable for Integer {
  fn format(&self, _formatter: &Formatter) -> String {
    format!("{}", self.0)
  }
}

impl NormalFormOrder for Integer {
  fn cmp(&self, other: &Self) -> Ordering {
    self.0.cmp(&other.0)
  }
}

impl Atom for Integer {
  fn hash(&self) -> u64 {
    // Numbers don't cache their hash.
    // if self.cached_hash != 0 {
    //   return self.cached_hash;
    // }

    let mut hasher = FnvHasher::default();

    hasher.write(&[242, 99 , 84 , 113, 102, 46 , 118, 94]);
    hasher.write_i64(self.0);

    let result       = hasher.finish();
    // self.cached_hash = result;

    result
  }

  fn to_expression(self) -> Expression {
    Expression::Integer(self)
  }


}

impl<T> From<T> for Integer
  where T: Into<i64>
{
  fn from(n: T) -> Self {
    Integer(n.into())
  }
}


impl From<Integer> for Expression {
  fn from(literal: Integer) -> Self {
    Expression::Integer(literal)
  }
}


display_formattable_impl!(Integer);
