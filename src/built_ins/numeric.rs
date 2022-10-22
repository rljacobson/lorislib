/*!

Numeric Computation

 */
#![allow(non_snake_case)]
use std::{
  rc::Rc
};
use std::collections::HashMap;
use std::ops::{AddAssign, Div, MulAssign, Neg};

use rug::{Integer as BigInteger, Float as BigFloat, Float, Assign, ops::AddFrom, Complete};
use rug::ops::CompleteRound;
use num_integer; // For num_integer::binomial

use crate::{
  matching::{
    display_solutions,
    SolutionSet
  },
  parse,
  atom::{
    Symbol,
    SExpression,
    SExpression::hold,
    Atom,
    AtomKind
  },
  attributes::{
    Attributes,
    Attribute
  },
  context::*,
  logging::{
    log,
    Channel
  },
  interner::{
    interned_static,
    InternedString
  },
  evaluate,
  matching::Matcher
};
use crate::built_ins::{DEFAULT_REAL_PRECISION, register_builtin};
#[allow(unused_imports)]#[allow(unused_imports)]
use crate::interner::resolve_str;
#[allow(unused_imports)]
use crate::logging::set_verbosity;


// todo: None of this code allows for BigReal precision other than the default 53 bits (f64).

/// Implements calls matching
///     `N[exp_] := built-in[exp_]`
// N[x] := built-in[{exp_->x}, context]
pub fn N(arguments: SolutionSet, _: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "N called with arguments {}",
      display_solutions(&arguments)
      // &arguments.iter().map(|(e, f)| {
      //   format!("{} -> {}", e.to_string(), f.to_string())
      // }
      // ).collect::<Vec<_>>().join(", ")
    ).as_str()
  );

  // The substitutions represent the parameters to `N`. In the case of `N`, there is only one variable in the lhs
  // pattern, so we're applying `N` to  whatever the rhs expression is.
  // `N` has already been threaded over expressions, so we only need to act on our one argument. Because of the
  // attributes of `N` (no `HoldFirst`, etc.), we can assume the argument has already been evaluated.
  let rhs = &arguments[&SExpression::variable_static_str("exp")];

  match rhs {

    Atom::Integer(n) => {
      let mut r: Float = BigFloat::new(DEFAULT_REAL_PRECISION);
      r.assign(n);
      return Atom::Real(r);
    }

    _other => {
      return rhs.clone();
    }
  } // end match on evaluated rhs.
}


/// Implements calls matching
///     `Plus[exp___] := built-in[exp___]`
pub fn Plus(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
  let mut int_accumulator       : BigInteger = BigInteger::new();
  let mut real_accumulator      : BigFloat   = BigFloat::new(DEFAULT_REAL_PRECISION);
  // We cannot just rely on whether or not `real_accumulator == 0.0` at the end, because `1 + 0.0 == 1.0`, not `1`.
  let mut real_value_encountered: bool       = false;

  log(
    Channel::Debug,
    4,
    format!(
      "Plus called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  // The argument should either be a `Sequence` or a single expression.
  let  rhs = &arguments[&SExpression::null_sequence_variable_static_str("exp")];
  // `new_children` is headless.
  let mut new_children: Vec<Atom> = Vec::new();

  if let Some(sequence_children) = rhs.is_sequence() {
    for expression in sequence_children {
      match expression {

        Atom::Integer(n) => {
          int_accumulator.add_assign(n);
        }

        Atom::Real(r) => {
          real_accumulator.add_assign(r);
          real_value_encountered = true;
        }

        other => {
          new_children.push(other);
        }
      }
    } // end iter over children

    // We have to do a little dance with the resulting type, because… l. On the other hand, if
    if real_value_encountered {
      // …if there were any reals, the numerical result is a real, even if `real_accumulator == 0.0`.
      // Since `BigInteger`s have infinite precision, we can just add `int_accumulator` without worrying if there
      // were any integers.
      real_accumulator.add_from(&int_accumulator);
      new_children.push(Atom::Real(real_accumulator));
    } else if int_accumulator != 0 {
      // …if there were no reals encountered but whatever integers there were summed to something non-zero,
      // the result is a `BigInteger`
      new_children.push(Atom::Integer(int_accumulator));
    } else {
      // …if there were no reals and whatever integers there were summed to 0, don't put any number in the result.
    }

    if new_children.len() == 0 {
      // The empty sum is zero.
      Atom::Integer(BigInteger::new())
    } else if new_children.len() == 1 {
      // OneIdentity: `Plus[e] = e`
      new_children[0].clone()
    } else {
      SExpression::new(Symbol::from_static_str("Plus"), new_children)
    }
  } // end if-let sequence
  else {
    // OneIdentity: `Plus[e] = e`
    rhs.clone()
  }

}

/// Implements calls matching
///     `Minus[exp_] := built-in[exp]`
pub fn Minus(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Minus called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );

  // The argument is a single expression
  let  rhs = &arguments[&SExpression::variable_static_str("exp")];
  match rhs {

    Atom::SExpression(children) if children[0]==Symbol::from_static_str("Minus") =>{
      children[1].clone()
    }


    Atom::Integer(n) => {
      Atom::Integer(n.neg().complete())
    }

    Atom::Real(r) => {
      Atom::Real(r.neg().complete(DEFAULT_REAL_PRECISION))
    }

    _ => rhs.clone()
  }

}

/// Implements calls matching
///     `Times[exp___] := built-in[exp___]`
pub fn Times(arguments: SolutionSet, _: Atom, _: &mut Context) -> Atom {

  let mut int_accumulator       : BigInteger = BigInteger::from(1);
  let mut real_accumulator      : BigFloat   = BigFloat::with_val(DEFAULT_REAL_PRECISION, 1f64);
  let mut real_value_encountered: bool       = false;

  // The argument should either be a `Sequence` or a single expression.
  let mut new_children: Vec<Atom> = Vec::new();
  let rhs = &arguments[&SExpression::null_sequence_variable_static_str("exp")];

  if let Some(sequence_children) = rhs.is_sequence() {
    for expression in &sequence_children {
      match expression {
        Atom::Integer(n) => {
          int_accumulator.mul_assign(n);
        }

        Atom::Real(r) => {
          real_accumulator.mul_assign(r);
          real_value_encountered = true;
        }

        _other => {
          new_children.push(expression.clone())
        }
      }
    } // end iter over children

    // We have to do a little dance with the resulting type, because… l. On the other hand, if
    if real_value_encountered {
      // …if there were any reals, the numerical result is a real, even if
      // `real_accumulator == 1.0`. Since `BigInteger`s have infinite precision, we can
      // just multiply `int_accumulator` without worrying if there were any integers.
      real_accumulator.mul_assign(int_accumulator);
      new_children.push(Atom::Real(real_accumulator));
    } else if int_accumulator != 1 {
      // …if there were no reals encountered but whatever integers there were multiplied to something different
      // from 1, the result is a`BigInteger
      new_children.push(Atom::Integer(int_accumulator));
    } else {
      // …if there were no reals and whatever integers there were multiplied to 1, don't put any number in the result.
    }

    if new_children.len() == 0 {
      // The empty product `Times[]` is 1.
      Atom::Integer(BigInteger::from(1))
    } else if new_children.len() == 1 {
      // OneIdentity: `Multiply[e] = e`
      new_children[0].clone()
    } else {
      SExpression::new(
        Symbol::from_static_str("Times"),
        new_children
      )
    }
  } // end if-let sequence
  else {
    // OneIdentity: `Times[e] = e`
    rhs.clone()
  }
}


/// Implements calls matching
///     `Divide[num_, denom_] := built-in[num_, denom_]`
pub fn Divide(arguments: SolutionSet, original_expression: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Divide called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );
  // Two arguments
  let numerator   = &arguments[&SExpression::variable_static_str("num")];
  let denominator = &arguments[&SExpression::variable_static_str("denom")];

  log(
    Channel::Debug,
    5,
    format!(
      "Dividing {} by {}.",
      &numerator,
      &denominator
    ).as_str()
  );

  match numerator {

    Atom::Real(r) if *r == 0  => {
      match denominator {
        | Atom::Real(_r2) if *_r2 == 0
        => Symbol::from_static_str("Indeterminate"),
        | Atom::Integer(_i) if *_i == 0
        => Symbol::from_static_str("Indeterminate"),

        _ => Atom::Real(BigFloat::new(DEFAULT_REAL_PRECISION)),
      }
    }

    Atom::Integer(n) if *n == 0 => {
      match denominator {
        Atom::Real(_r) if *_r == 0
        => { Symbol::from_static_str("Indeterminate")},
        Atom::Integer(_m) if *_m == 0
        => { Symbol::from_static_str("Indeterminate")},

        Atom::Real(_)    => { Atom::Real(BigFloat::new(DEFAULT_REAL_PRECISION)) },

        _ => Atom::Integer(BigInteger::new()),
      }
    }

    Atom::Real(num) if *num != 0f64 => {
      match denominator {
        Atom::Real(_r) if *_r == 0
        => { Symbol::from_static_str("ComplexInfinity")},
        Atom::Integer(_m) if *_m == 0
        => { Symbol::from_static_str("ComplexInfinity")},

        Atom::Real(denom)    => {
          log(

            Channel::Debug,
            5,
            format!(
              "Dividing {} by {}.",
              num,
              denom
            ).as_str()
          );
          Atom::Real(num.div(denom).complete(DEFAULT_REAL_PRECISION))
        },

        Atom::Integer(denom) => Atom::Real(num.div(denom).complete(DEFAULT_REAL_PRECISION)),

        _ => { original_expression }
      }
    }

    Atom::Integer(num) if *num != 0 => {
      match denominator {
        | Atom::Real(_r) if *_r == 0
        => Symbol::from_static_str("ComplexInfinity"),
        | Atom::Integer(_n) if *_n == 0
        => Symbol::from_static_str("ComplexInfinity"),

        Atom::Real(denom) => Atom::Real((num/denom).complete(DEFAULT_REAL_PRECISION)),

        Atom::Integer(denom) => {
          // todo: Implement `Rational`.
          let common_divisor = BigInteger::gcd(num.clone(), &denom);
          let reduced_num    = Atom::Integer(num.div(&common_divisor).complete());
          let reduced_denom  = Atom::Integer(denom.div(&common_divisor).complete());

          Atom::SExpression(Rc::new(
            [
              Symbol::from_static_str("Divide"),
              reduced_num,
              reduced_denom
            ].to_vec()
          ))
        }

        _ => { original_expression }
      }
    }

    _other => {
      match denominator {
        | Atom::Real(_r) if *_r == 0
        => Symbol::from_static_str("ComplexInfinity"),
        | Atom::Integer(_n) if *_n == 0
        => Symbol::from_static_str("ComplexInfinity"),

        _ => original_expression
      }
    }

  } // end match numerator
}


/// Implements calls matching
///     `Binomial[n_, m_] := builtin[n,m]`
pub fn Binomial(arguments: SolutionSet, original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Divide called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );
  // Two arguments
  let n = &arguments[&SExpression::variable_static_str("n")];
  let m = &arguments[&SExpression::variable_static_str("m")];

  log(
    Channel::Debug,
    5,
    format!(
      "Calling Binomial with {} by {}.",
      &n,
      &m
    ).as_str()
  );

  match (n, m) {
    (Atom::Integer(n), Atom::Integer(m)) => {
      match m.try_into() {
        Ok(m) => {
          Atom::Integer(n.clone().binomial(m))
        }

        Err(_) => {
          log(
            Channel::Error,
            1,
            "Arguments to Binomial are out of range."
          );
          original
        }
      }
    }

    (Atom::Real(_), Atom::Integer(_))
    | (Atom::Integer(_), Atom::Real(_)) => {
      log(
        Channel::Error,
        1,
        "Arguments to Binomial must be integers."
      );
      original
    }

    _ => original

  }



}



pub(crate) fn register_builtins(context: &mut Context) {
  // A set of common attributes for convenience.
  let read_only_attributes: Attributes = Attribute::ReadOnly + Attribute::AttributesReadOnly;

  // Numeric Floating Point Conversion
  register_builtin!(N, "N[exp_]", Attribute::Protected+Attribute::Listable, context);
  register_builtin!(Minus, "Minus[exp_]", Attribute::Protected+Attribute::Listable, context);

  let plus_attributes
      = read_only_attributes +
      Attribute::Associative +
      Attribute::Commutative +
      Attribute::Variadic +
      Attribute::OneIdentity;
  register_builtin!(Plus, "Plus[exp___]", plus_attributes, context);
  // Same attributes as Plus
  register_builtin!(Times, "Times[exp___]", plus_attributes, context);
  register_builtin!(Divide, "Divide[num_, denom_]", read_only_attributes, context);
  register_builtin!(Binomial, "Binomial[n_, m_]", read_only_attributes + Attribute::NHoldAll, context);

}
