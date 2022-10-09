/*!

Real number primitive type. Since this is just a proof of concept, reals are represented by `f64`s.

Todo: Use Rug for arbitrary precision.

*/

use std::{
  cmp::Ordering,
  hash::Hasher,
  convert::{From, Into},
};
use std::mem::transmute;
use fnv::FnvHasher;

use crate::{format::{
  Formattable,
  Formatter
}, normal_form::NormalFormOrder, expression::Expression, RcExpression};
use crate::atoms::unwrap_atom_impl;

use super::Atom;


#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Real(pub f64);

unwrap_atom_impl!(Real);

impl Formattable for Real {
  fn format(&self, _formatter: &Formatter) -> String {
    format!("{}", self.0)
  }
}

impl Eq for Real {}

impl Ord for Real {
  fn cmp(&self, other: &Self) -> Ordering {
    self.0.total_cmp(&other.0)
  }
}

impl NormalFormOrder for Real {
  fn cmp(&self, other: &Self) -> Ordering {
    self.0.total_cmp(&other.0)
  }
}

impl Atom for Real {
  fn hash(&self) -> u64 {
    // Reals don't cache their hash.
    // if self.cached_hash != 0 {
    //   return self.cached_hash;
    // }

    let mut hasher = FnvHasher::default();

    hasher.write(&[195, 244, 76 , 249, 227, 115, 88 , 251]);
    let val: u64 = unsafe{transmute(self.0)};
    hasher.write_u64(val);

    let result = hasher.finish();
    // self.cached_hash = result;

    result
  }

  fn to_expression(self) -> Expression {
    Expression::Real(self)
  }


}

impl<T> From<T> for Real
  where T: Into<f64>
{
  fn from(n: T) -> Self {
    Real(n.into())
  }
}

impl From<Real> for Expression {
  fn from(literal: Real) -> Self {
    Expression::Real(literal)
  }
}


display_formattable_impl!(Real);
