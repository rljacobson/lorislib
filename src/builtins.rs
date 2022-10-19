#![allow(non_snake_case)]
/*!

Built-in constants and functions.

 */

use std::{
  rc::Rc
};
use std::ops::{AddAssign, Div, MulAssign};

use rug::{
  Integer as BigInteger,
  Float as BigFloat,
  Float,
  Assign,
  ops::AddFrom
};

use crate::{
  parse,
  atom::{
    Atom,
    SExpression,
    Symbol
  },
  attributes::{Attribute, Attributes},
  context::*,
  evaluate::evaluate,
  logging::{Channel, log},
  matching::SolutionSet,
  interner::{interned_static, InternedString}
};


// todo: store this in the global context as an own-value.
pub const DEFAULT_REAL_PRECISION: u32 = 53;

// need: And, NumberQ, SameQ, Occurs

pub static STANDARD_PREAMBLE: [&str; 14] = [
  "Condition[f_[x_, y_], z_]:=f_[x_, y_, z_]",

  // Definitions
  "Subtract[x_, rest___]:=Plus[x_, Times[-1, Plus[rest___]]]",
  "Sqrt[x_]:=Root[2, x_]", // Poorly named, perhaps.
  "Ln[x_]:=Log[E, x_]",
  "Exp[x_]:=Power[E, x_]",

  // Simplifications
  "a_*x_ + b_*y_ ^:= (a_ + b_)*x_ /; And[SameQ[x_, y_], NumberQ[a_], NumberQ[b_]]",
  "(a_*x_)/(b_*y_) ^:= a_ / b_ /; SameQ[x_, y_]",

  // Differentiation
  "D[x_, y_] := 0 /; NumberQ[x_]",                                  // Constants. No matching on `Head`
  "D[x_, y_] := 1 /; SameQ[x_, y_]",                                // Identity
  "D[x_^n_, y_] ^:= n*x_^(n-1)*D[x_, y_] /; Occurs[y_, x_]", // Power Rule,

  "D[Sin[x_], y_] ^:= Cos[x_]*D[x_, y_] /; Occurs[y_, x_]",
  "D[Cos[x_], y_] ^:= -Sin[x_]*D[x_, y_] /; Occurs[y_, x_]",
  "D[Tan[x_], y_] ^:= Sec[x_]^2*D[x_, y_] /; Occurs[y_, x_]",
  "D[Sec[x_], y_] ^:= Sec[x_]*Tan[x_]*D[x_, y_] /; Occurs[y_, x_]",
];


//                        f(substitutions, original_expression, context) -> evaluated_expression
pub(crate) type BuiltinFn = fn(SolutionSet, Atom, &mut Context) -> Atom;


// region Numeric Computation
// todo: None of this code allows for BigReal precision other than the default 53 bits (f64).

/// Implements calls matching
///     `N[exp_] := built-in[exp_]`
// N[x] := built-in[{exp_->x}, context]
pub fn N(arguments: SolutionSet, _: Atom, _: &mut Context) -> Atom {
  // The substitutions represent the parameters to `N`. In the case of `N`, there is only one variable in the lhs
  // pattern, so we're applying `N` to  whatever the rhs expression is.
  // `N` has already been threaded over expressions, so we only need to act on our one argument. Because of the
  // attributes of `N` (no `HoldFirst`, etc.), we can assume the argument has already been evaluated.
  for (lhs, rhs) in arguments {
    log(
      Channel::Debug,
      5,
      format!("Built-in function N given arguments: ({:?}, {:?})", &lhs, &rhs).as_str()
    );
    // There is guaranteed to be one and only one substitution.
    match &rhs {

      Atom::Integer(n) => {
        let mut r: Float = BigFloat::new(DEFAULT_REAL_PRECISION);
        r.assign(n);
        return Atom::Real(r);
      }

      _other => {
        return rhs;
      }
    } // end match on evaluated rhs.
  }
  unreachable!("Built-in function `N` was called without arguments, which should be impossible. This is a bug.");
}


/// Implements calls matching
///     `Plus[exp___] := built-in[exp___]`
pub fn Plus(arguments: SolutionSet, _original: Atom, _: &mut Context) -> Atom {
  let mut int_accumulator       : BigInteger = BigInteger::new();
  let mut real_accumulator      : BigFloat   = BigFloat::new(DEFAULT_REAL_PRECISION);
  // We cannot just rely on whether or not `real_accumulator == 0.0` at the end, because `1 + 0.0 == 1.0`, not `1`.
  let mut real_value_encountered: bool       = false;

  // The argument should either be a `Sequence` or a single expression.
  let  (_lhs, rhs) = &arguments.iter().next().unwrap();
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
    (**rhs).clone()
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
  let  (_lhs, rhs) = &arguments.iter().next().unwrap();

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
    (**rhs).clone()
  }
}


/// Implements calls matching
///     `Divide[num_, denom_] := built-in[num_, denom_]`
pub fn Divide(arguments: SolutionSet, original_expression: Atom, _: &mut Context) -> Atom {
  // Two arguments
  let arg_pairs: Vec<_> = arguments.into_iter().collect();
  let (_, numerator) = arg_pairs[0].clone();
  let (_, denominator) = arg_pairs[1].clone();

  match numerator {

    Atom::Real(r) if r == 0  => {
      match denominator {
        | Atom::Real(_r2) if _r2 == 0
          => Symbol::from_static_str("Indeterminate"),
        | Atom::Integer(_i) if _i == 0
          => Symbol::from_static_str("Indeterminate"),

        _ => Atom::Real(BigFloat::new(DEFAULT_REAL_PRECISION)),
      }
    }

    Atom::Integer(n) if n == 0 => {
      match denominator {
        Atom::Real(_r) if _r == 0
          => { Symbol::from_static_str("Indeterminate")},
        Atom::Integer(_m) if _m == 0
          => { Symbol::from_static_str("Indeterminate")},

        Atom::Real(_)    => { Atom::Real(BigFloat::new(DEFAULT_REAL_PRECISION)) },

        _ => Atom::Integer(BigInteger::new()),
      }
    }

    Atom::Real(num) if num != 0f64 => {
      match denominator {
        Atom::Real(_r) if _r == 0
          => { Symbol::from_static_str("ComplexInfinity")},
        Atom::Integer(_m) if _m == 0
          => { Symbol::from_static_str("ComplexInfinity")},

        Atom::Real(denom)    => Atom::Real(num.div(denom)),

        Atom::Integer(denom) => Atom::Real(num.div(denom)),

        _ => { original_expression }
      }
    }

    Atom::Integer(num) if num != 0 => {
      match denominator {
        | Atom::Real(_r) if _r == 0
          => Symbol::from_static_str("ComplexInfinity"),
        | Atom::Integer(_n) if _n == 0
          => Symbol::from_static_str("ComplexInfinity"),

        Atom::Real(denom) => Atom::Real(num/denom),

        Atom::Integer(denom) => {
          // todo: Implement `Rational`.
          let common_divisor = BigInteger::gcd(num.clone(), &denom);
          let reduced_num    = Atom::Integer(num.div(&common_divisor));
          let reduced_denom  = Atom::Integer(denom.div(&common_divisor));

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
        | Atom::Real(_r) if _r == 0
          => Symbol::from_static_str("ComplexInfinity"),
        | Atom::Integer(_n) if _n == 0
          => Symbol::from_static_str("ComplexInfinity"),

        _ => original_expression
      }
    }

  } // end match numerator
}


// endregion

// region Context Manipulation

/// Implements calls matching the pattern
///     `Set[x_, rhs_]`
fn Set(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  // Two arguments
  let arg_pairs: Vec<_> = arguments.into_iter().collect();
  let (_, pattern) = arg_pairs[0].clone();

  let (rhs, condition): (Atom, Option<Atom>) = { // scope of inner rhs
    let (_, rhs) = arg_pairs[1].clone();
    extract_condition(rhs)
  };

  let value = SymbolValue::Definitions {
    def: original,
    lhs: pattern.clone(),
    rhs: rhs.clone(),
    condition,
  };

  match context.set_down_value(pattern.name().unwrap(), value) {
    Ok(()) => {}
    Err(msg) => {
      // todo: Make a distinction between program and system errors.
      log(Channel::Error, 1, msg.as_str());
    }
  };

  rhs.clone()
}


/// Implements calls matching the pattern
///     `UpSet[f_[___], rhs_]`
fn UpSet(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  // Two arguments
  let arg_pairs: Vec<_> = arguments.into_iter().collect();
  let (_  , pattern)    = arg_pairs[0].clone();
  let (_  , outer_rhs)  = arg_pairs[1].clone();
  let (rhs, condition): (Atom , Option<Atom>) = extract_condition(outer_rhs.clone());

  let value = SymbolValue::Definitions {
    def: original,
    lhs: pattern.clone(),
    rhs: rhs.clone(),
    condition,
  };

  for symbol in collect_symbol_or_head_symbol(pattern) {
    // Make an up-value for symbol
    match context.set_up_value(symbol, value.clone()) {
      Ok(()) => {}
      Err(msg) => {
        // todo: Make a distinction between program and system errors.
        log(Channel::Error, 1, msg.as_str());
      }
    }
  };

  outer_rhs
}

// endregion

pub(crate) fn register_builtins(context: &mut Context) {
  let mut read_only_attributes = Attributes::default();
  // todo: when is something read-only vs protected?
  read_only_attributes.set(Attribute::ReadOnly);
  read_only_attributes.set(Attribute::AttributesReadOnly);

  // region Context Manipulation
  // Set[lhs_, rhs_]
  let value = SymbolValue::BuiltIn{
    pattern  : parse("Set[lhs_, rhs_]").unwrap(),
    condition: None,
    built_in : Set
  };
  context.set_down_value_attribute(interned_static("Set"), value, read_only_attributes);

  // UpSet[lhs_, rhs_]
  let value = SymbolValue::BuiltIn{
    pattern  : parse("UpSet[lhs_, rhs_]").unwrap(),
    condition: None,
    built_in : UpSet
  };
  context.set_down_value_attribute(interned_static("UpSet"), value, read_only_attributes);

  // endregion

  // region Numeric Computation

  // Numeric Floating Point Conversion
  // N[e_Integer]:=e_Real
  let value = SymbolValue::BuiltIn{
    pattern  : parse("N[e_]").unwrap(),
    condition: None,
    built_in : N
  };
  let mut attributes = read_only_attributes;
  attributes.set(Attribute::Listable);
  context.set_down_value_attribute(interned_static("N"), value, attributes);

  // Plus[exp___]
  let value = SymbolValue::BuiltIn{
    pattern  : parse("Plus[e___]").unwrap(),
    condition: None,
    built_in : Plus
  };
  let mut attributes = read_only_attributes;
  attributes.set(Attribute::Associative);
  attributes.set(Attribute::Commutative);
  attributes.set(Attribute::Variadic);
  attributes.set(Attribute::OneIdentity);
  context.set_down_value_attribute(interned_static("Plus"), value, attributes);

  // Times[exp___]
  let value = SymbolValue::BuiltIn{
    pattern  : parse("Times[e___]").unwrap(),
    condition: None,
    built_in : Times
  };
  let mut attributes = read_only_attributes;
  attributes.set(Attribute::Associative);
  attributes.set(Attribute::Commutative);
  attributes.set(Attribute::Variadic);
  attributes.set(Attribute::OneIdentity);
  context.set_down_value_attribute(interned_static("Times"), value, attributes);

  // Divide[exp1, exp2]
  let value = SymbolValue::BuiltIn{
    pattern  : parse("Divide[exp1_, exp2_]").unwrap(),
    condition: None,
    built_in : Divide
  };
  context.set_down_value_attribute(interned_static("Divide"), value, read_only_attributes);

  // endregion

  // region Constants
  // Todo: Implement NValues

  // Numeric up_value for `Pi`
  { // Scope for pi_record
    let mut pi_record = context.get_symbol_mut(interned_static("Pi"));
    let f = { // scope of children
      let children = [
        Symbol::from_static_str("UpSet"),
        Atom::SExpression(Rc::new(
          [
            Symbol::from_static_str("N"),
            Symbol::from_static_str("Pi")
          ].to_vec()
        )),
        Atom::Real(BigFloat::with_val(53, rug::float::Constant::Pi))
      ];
      Atom::SExpression(Rc::new(children.to_vec()))
    };

    evaluate(f, context);
  }

  // endregion

}

// region utilities

/// If `atom` has the form `Condition[exp1, exp2]`, gives `(exp1, Some(exp2))`. Otherwise, gives `(atom, None)`.
fn extract_condition(atom: Atom) -> (Atom, Option<Atom>) {
  match atom {

    Atom::SExpression(children)
      if children.len() == 3 && children[0] == Symbol::from_static_str("Condition")
      => {
      (children[1].clone(), Some(children[2].clone()))
    }

    _ => (atom, None)
  }
}

/// The `pattern_function` must be a function. Finds all symbols or symbols that are heads of functions that are
/// arguments to the given function.
fn collect_symbol_or_head_symbol(pattern_function: Atom) -> Vec<InternedString>{
  let f = SExpression::children(&pattern_function);
  let mut child_iter = f.iter();
  child_iter.next(); // skip head

  child_iter.filter_map(|c| {
    match c {
      Atom::Symbol(name) => Some(*name),
      Atom::SExpression(f)=> Some(f[0].name().unwrap()),
      _ => None
    }
  }).collect()
}



// endregion

#[cfg(test)]
mod tests {
  #[test]
  fn it_works() {
    assert_eq!(2 + 2, 4);
  }
}
