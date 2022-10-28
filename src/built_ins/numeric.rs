/*!

Numeric Computation

 */
#![allow(non_snake_case)]

use std::{
  rc::Rc,
  ops::{AddAssign, Div, MulAssign, Neg}
};

use rug::{
  Integer as BigInteger,
  Float as BigFloat,
  Float,
  Assign,
  ops::{
    AddFrom,
    CompleteRound,
    Pow
  },
  Complete,
};
// For num_integer::binomial

use crate::{
  evaluate::{
    evaluate,
    replace_all_bound_variables
  },
  interner::{
    interned_static
  },
  logging::{
    log,
    Channel
  },
  context::*,
  attributes::{
    Attributes,
    Attribute
  },
  parse,
  matching::{
    display_solutions,
    SolutionSet
  },
  atom::{
    SExpression::apply,
    Atom,
    SExpression,
    Symbol,
    SExpression::apply_binary
  },
  built_ins::{
    DEFAULT_REAL_PRECISION,
    register_builtin
  }
};


// todo: None of this code allows for BigReal precision other than the default 53 bits (f64).

/// Implements calls matching
///     `N[exp_] := built-in[exp_]`
// N[x] := built-in[{exp_->x}, context]
pub(crate) fn N(arguments: SolutionSet, _: Atom, _: &mut Context) -> Atom {
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
pub(crate) fn Plus(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
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
pub(crate) fn Minus(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
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

    _ => {
      apply_binary(
        "Times",
        Atom::Integer(BigInteger::from(-1)),
        rhs.clone()
      )
    }
  }

}

/// Implements calls matching
///     `Times[exp___] := built-in[exp___]`
pub(crate) fn Times(arguments: SolutionSet, _: Atom, _: &mut Context) -> Atom {

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
pub(crate) fn Divide(arguments: SolutionSet, original_expression: Atom, _: &mut Context) -> Atom {
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

          apply_binary("Divide", reduced_num, reduced_denom)
        }

        _ => { original_expression }
      }
    }

    _other => {
      match denominator {
        Atom::Real(_r) if *_r == 0
          => Symbol::from_static_str("ComplexInfinity"),
        Atom::Integer(_n) if *_n == 0
          => Symbol::from_static_str("ComplexInfinity"),

        Atom::Real(_r) if *_r == 1.0
          => numerator.clone(),

        Atom::Integer(_n) if *_n == 1
          => numerator.clone(),

        _ => original_expression
      }
    }

  } // end match numerator
}


/// Implements calls matching
///     `Binomial[n_, m_] := builtin[n,m]`
pub(crate) fn Binomial(arguments: SolutionSet, original: Atom, _: &mut Context) -> Atom {
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

/// Implements calls matching
///     `Power[base_, exp_]`
pub(crate) fn Power(arguments: SolutionSet, original: Atom, _: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Power called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );
  // Two arguments
  let base = &arguments[&SExpression::variable_static_str("base")];
  let exp = &arguments[&SExpression::variable_static_str("exp")];

  match (base, exp) {
    (Atom::Integer(n), Atom::Integer(m)) => {
      let result: BigInteger = n.clone();
      // todo: We have to decide how to handle reciprocals and stuff.
      if m < &0i32 {
        // We compute n^-m and then return the reciprocal.
        let positive_exponent = m.clone().neg();
        let within_range: u32 = match positive_exponent.try_into() {
          Ok(v) => v,
          Err(_) => {
            log(
              Channel::Error,
              1,
          "Exponent is out of range."
            );
            return original;
          }
        };
        let result = result.pow(within_range);

        apply_binary(
          "Divide",
          Atom::Integer(BigInteger::from(1)),
          Atom::Integer(result)
        )
      } else if m == &0 {
        if n == &0 {
          Symbol::from_static_str("Indeterminate")
        } else {
          Atom::Integer(BigInteger::from(1))
        }
      } else {
        let within_range: u32 = match m.try_into() {
          Ok(v) => v,
          Err(e) => {
            log(
              Channel::Error,
              1,
              format!("Exponent is out of range: {}", e).as_str(),
            );
            return original;
          }
        };
        let result = result.pow(within_range);
        Atom::Integer(result)
      }
    } // end branch if both are integers

    (Atom::Real(r), Atom::Integer(m)) => {
      let result: BigFloat = r.clone();
      if m < &0i32 {
        // We compute n^-m and then return the reciprocal: // r^-p = 1/(r^p)
        let positive_exponent = m.clone().neg();
        let within_range: u32 = match positive_exponent.try_into() {
          Ok(v) => v,
          Err(_) => {
            log(
              Channel::Error,
              1,
              "Exponent is out of range."
            );
            return original;
          }
        };
        let result: BigFloat = result.pow(within_range);
        // r^-m = 1/(r^m)
        Atom::Real(result.recip())
      } else if m == &0 {
        if r.is_zero() {
          Symbol::from_static_str("Indeterminate")
        } else{
          Atom::Real(BigFloat::with_val(DEFAULT_REAL_PRECISION, 1))
        }
      } else {
        let within_range: u32 = match m.try_into() {
          Ok(v) => v,
          Err(_) => {
            log(
              Channel::Error,
              1,
              "Exponent is out of range."
            );
            return original;
          }
        };
        let result = result.pow(within_range);
        Atom::Real(result)
      }
    }

    (Atom::Integer(n), Atom::Real(r)) => {
      // todo: Complex numbers from fractional roots
      if n < &0 && r < &1.0 && r > &-1.0 {
        log(Channel::Error, 1, "Complex numbers haven't been invented yet.");
        original
      }
      else if n == &0 && r.is_zero() {
        Symbol::from_static_str("Indeterminate")
      } else if n == &0 {
        Atom::Integer(BigInteger::from(0))
      } else if r.is_zero() {
        Atom::Real(BigFloat::with_val(DEFAULT_REAL_PRECISION, 1))
      } else {
        let real_n = BigFloat::with_val(DEFAULT_REAL_PRECISION,n);
        Atom::Real(real_n.pow(r))
      }
    }

    _ => {
      // We do not automatically expand things like (1+x)^2
      original
    }

  }
}


/// Implements calls matching
///     `Series[f_, {x_, c_, n_}] := builtin[n,m]`
// Todo: Rewrite this using list primitives when they exist. Or not?
pub(crate) fn Series(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  log(
    Channel::Debug,
    4,
    format!(
      "Series called with arguments {}",
      display_solutions(&arguments)
    ).as_str()
  );
  // Two arguments
  let f = &arguments[&SExpression::variable_static_str("f")];
  let x_variable = SExpression::variable_static_str("x"); // We'll need this again later.
  let x = &arguments[&x_variable];
  let c = &arguments[&SExpression::variable_static_str("c")];
  let n = &arguments[&SExpression::variable_static_str("n")];

  let n: u32 = match n {
    Atom::Integer(m) => m.to_u32_wrapping(),
    other => {
      log(
        Channel::Error,
        1,
        format!(
          "Series order needs to be a nonnegative integer. Got {}.",
          other
        ).as_str()
      );
      return original;
    }
  };

  let x_to_c: SolutionSet = SolutionSet::from([(x_variable, c.clone())]);
  let mut new_children: Vec<Atom> = Vec::with_capacity(n as usize + 2); // Includes the head and the order
  new_children.push(Symbol::from_static_str("Plus")); // Head
  // The zeroth derivative: evaluate f[c]
  new_children.push(replace_all_bound_variables(f.clone(), &x_to_c, context));

  // Derivatives 1 through n
  let mut derivative: Atom = f.clone();
  for m in 1..n {
    derivative = // D[derivative, x]
        evaluate(
          apply_binary("D", derivative.clone(), x.clone()),
          context
        );

    let coeff: Atom = // f^{(m)}(c)/m!
        apply_binary(
          "Divide",
          replace_all_bound_variables(derivative.clone(), &x_to_c, context),
          Atom::Integer(BigInteger::factorial(m).complete())
        );

    let monomial: Atom = // (x-c)^m
        apply_binary(
          "Power",
          apply_binary("Subtract", x.clone(), c.clone()),
          Atom::Integer(BigInteger::from(m))
        );

    new_children.push(apply_binary("Times", coeff, monomial))
  }

  // + O[n+1]
  new_children.push(apply("O", Atom::Integer(BigInteger::from(n+1))));

  Atom::SExpression(Rc::new(new_children))
}


pub(crate) fn register_builtins(context: &mut Context) {
  // A set of common attributes for convenience.
  let read_only_attributes: Attributes = Attribute::ReadOnly + Attribute::AttributesReadOnly;

  // Numeric Floating Point Conversion
  register_builtin!(N, "N[exp_]", Attribute::Protected+Attribute::Listable, context);
  register_builtin!(Minus, "Minus[exp_]", Attribute::Protected.into(), context);

  let plus_attributes
      = read_only_attributes +
      Attribute::Associative +
      Attribute::Commutative +
      Attribute::Variadic +
      Attribute::OneIdentity;
  register_builtin!(Plus, "Plus[exp___]", plus_attributes, context);
  // Same attributes as Plus
  register_builtin!(Times, "Times[exp___]", plus_attributes, context);
  register_builtin!(Binomial, "Binomial[n_, m_]", read_only_attributes + Attribute::NHoldAll, context);
  register_builtin!(Divide, "Divide[num_, denom_]", read_only_attributes, context);
  register_builtin!(Power, "Power[base_, exp_]", read_only_attributes, context);
  register_builtin!(Series, "Series[f_, {x_, c_, n_}]", Attribute::Protected.into(), context);

}
