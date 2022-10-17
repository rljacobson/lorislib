#![allow(non_snake_case)]
/*!

Built-in constants and functions.

 */

use std::{
  collections::HashMap,
  rc::Rc
};

use crate::{
  expression::Expression,
  parse,
  atom::Atom,
  attributes::{Attribute, Attributes},
  context::*,
  evaluate::evaluate,
  logging::{Channel, log},
  matching::SolutionSet
};
// use std::f64::consts;


//                        f(substitutions, original_expression, context) -> evaluated_expression
pub(crate) type BuiltinFn = fn(SolutionSet, Atom, &mut Context) -> Atom;

/*
pub static CONSTANTS: HashMap<&'static str, f64> = HashMap::from( [
  ( "Pi", std::f64::consts::PI ),
  ( "TAU", std::f64::consts::TAU ),
  ( "E", std::f64::consts::E ),

] );
*/

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


// region Numeric Computation

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
      format!("Built-in function N given argumetns: {:?}", (&lhs, &rhs)).as_str()
    );
    // There is guaranteed to be one and only one substitution.
    match rhs.as_ref() {

      Atom::Integer(n) => {
        return Rc::new(Atom::Real(*n as f64));
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
pub fn Plus(arguments: SolutionSet, _: Atom, _: &mut Context) -> Atom {
  let mut int_accumulator = 0i64;
  let mut real_accumulator = 0f64;

  // The argument should either be a `Sequence` or a single expression.
  for (lhs, rhs) in arguments {
    let mut new_children: Vec<Atom> = Vec::new();

    if let Expression::Sequence(sequence) = rhs.as_ref() {
      for expression in &sequence.children {
        match expression.as_ref() {

          Atom::Integer(n) => {
            int_accumulator += n;
          }

          Atom::Real(r) => {
            real_accumulator += r;
          }

          _other => {
            new_children.push(expression.clone())
          }
        }
      } // end iter over children

      if int_accumulator != 0 && real_accumulator != 0f64 {
        let sum = Atom::Real(real_accumulator + int_accumulator as f64);
        new_children.push(Rc::new(sum));
      } else if int_accumulator != 0 {
        new_children.push(Rc::new(Atom::Integer(int_accumulator)));
      } else if real_accumulator != 0f64 {
        new_children.push(Rc::new(Atom::Real(real_accumulator)));
      }

      if new_children.len() == 1 {
        // OneIdentity: `Plus[e] = e`
        return new_children[0].clone();
      }

      let mut plus = Function::with_symbolic_head("Plus");
      plus.children = new_children;

      return Rc::new(plus.into())
    } // end if-let sequence
    else {

      // OneIdentity: `Plus[e] = e`
      return rhs;

    }
  }

  // The empty sum is zero.
  Rc::new(Integer(0).into())
}


/// Implements calls matching
///     `Times[exp___] := built-in[exp___]`
pub fn Times(arguments: SolutionSet, _: Atom, _: &mut Context) -> Atom {
  let mut int_accumulator = 1i64;
  let mut real_accumulator = 1f64;

  // The argument should either be a `Sequence` or a single expression.
  for (lhs, rhs) in arguments {
    let mut new_children: Vec<Atom> = Vec::new();

    if let Expression::Sequence(sequence) = rhs.as_ref() {
      for expression in &sequence.children {
        match expression.as_ref() {

          Atom::Integer(n) => {
            int_accumulator *= n;
          }

          Atom::Real(r) => {
            real_accumulator *= r;
          }

          _other => {
            new_children.push(expression.clone())
          }
        }
      } // end iter over children

      if int_accumulator != 1 && real_accumulator != 1f64 {
        let sum = Atom::Real(real_accumulator + int_accumulator as f64);
        new_children.push(Rc::new(sum));
      } else if int_accumulator != 1 {
        new_children.push(Rc::new(Atom::Integer(int_accumulator)));
      } else if real_accumulator != 1f64 {
        new_children.push(Rc::new(Atom::Real(real_accumulator)));
      }

      if new_children.len() == 1 {
        // OneIdentity: `Plus[e] = e`
        return new_children[0].clone();
      }

      let mut plus = Function::with_symbolic_head("Plus");
      plus.children = new_children;

      return Rc::new(plus.into())
    } // end if-let sequence
    else {

      // OneIdentity: `Times[e] = e`
      return rhs;

    }
  }

  // The empty product is 1.
  Rc::new(Integer(1).into())
}


/// Implements calls matching
///     `Divide[num_, denom_] := built-in[num_, denom_]`
pub fn Divide(arguments: SolutionSet, original_expression: Atom, _: &mut Context) -> Atom {
  // Two arguments
  let arg_pairs: Vec<_> = arguments.into_iter().collect();
  let (_, numerator) = arg_pairs[0].clone();
  let (_, denominator) = arg_pairs[1].clone();

  match numerator.as_ref() {

    Atom::Real(0f64)  => {
      match denominator.as_ref() {
        | Atom::Real(0f64)
        | Atom::Integer(0)
          => Rc::new(Symbol::from("Indeterminate").into()),

        _ => Rc::new(Real(0f64).into()),
      }
    }

    Atom::Integer(0) => {
      match denominator.as_ref() {
        | Atom::Real(0f64)
        | Atom::Integer(0)
          => { return Rc::new(Symbol::from("Indeterminate").into()); },

        Expression::Real(_)    => { return Rc::new(Real(0f64).into()); },
        Expression::Integer(_) => { return Rc::new(Integer(0).into()); },

        _ => Rc::new(Integer(0).into()),
      }
    }

    Atom::Real(num) if *num != 0f64 => {
      match denominator.as_ref() {
        | Atom::Real(0f64)
        | Expression::Integer((Integer(0)))
        => Rc::new(Symbol::from("ComplexInfinity").into()),

        Atom::Real(denom) => Rc::new(Real(num/denom).into()),

        Atom::Integer(denom) => Rc::new(Real(num/(*denom as f64)).into()),

        _ => { original_expression }
      }
    }

    Atom::Integer(num) if *num != 0 => {
      match denominator.as_ref() {
        | Atom::Real(0f64)
        | Expression::Integer((Integer(0)))
        => Rc::new(Symbol::from("ComplexInfinity").into()),

        Atom::Real(denom) => Rc::new(Real(*num as f64/denom).into()),

        Atom::Integer(denom) => {
          let common_divisor = gcd(*num, *denom);
          let reduced_num = Rc::new(Integer(num/common_divisor).into());
          let reduced_denom = Rc::new(Integer(denom/common_divisor).into());
          let mut f = Function::with_symbolic_head("Divide");
          f.children.push(reduced_num);
          f.children.push(reduced_denom);
          Rc::new(f.into())
        }

        _ => { original_expression }
      }
    }

    other => {
      match denominator.as_ref() {
        | Atom::Real(0f64)
        | Expression::Integer((Integer(0)))
          // This isn't very conservative, but it's what Mathematica does.
          => Rc::new(Symbol::from("ComplexInfinity").into()),

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
  let (_, rhs) = arg_pairs[1].clone();

  let value = SymbolValue::Definitions {
    def: original,
    lhs: pattern.clone(),
    rhs: rhs.clone(),
    condition: None,
  };

  match context.set_down_value(pattern.name(), value.clone()) {
    Ok(()) => {}
    Err(msg) => {
      // todo: Make a distinction between program and system errors.
      log(Channel::Error, 1, msg.as_str());
    }
  };
  rhs
}


/// Implements calls matching the pattern
///     `UpSet[f_[___], rhs_]`
fn UpSet(arguments: SolutionSet, original: Atom, context: &mut Context) -> Atom {
  // Two arguments
  let arg_pairs: Vec<_> = arguments.into_iter().collect();
  let (_, pattern) = arg_pairs[0].clone();
  let (_, rhs) = arg_pairs[1].clone();

  let value = SymbolValue::Definitions {
    def: original,
    lhs: pattern.clone(),
    rhs: rhs.clone(),
    condition: None,
  };

  for symbol in collect_symbol_or_head_symbol(pattern) {
    // Make an up-value for symbol
    match context.set_up_value(symbol.name(), value.clone()) {
      Ok(()) => {}
      Err(msg) => {
        // todo: Make a distinction between program and system errors.
        log(Channel::Error, 1, msg.as_str());
      }
    }
  };
  rhs
}

// endregion

pub(crate) fn register_builtins(context: &mut Context) {
  let mut parser = Parser::new();
  let mut read_only_attributes = Attributes::default();
  read_only_attributes.set(Attribute::ReadOnly);
  read_only_attributes.set(Attribute::AttributesReadOnly);

  // region Context Manipulation
  // Set[lhs_, rhs_]
  let value = SymbolValue::BuiltIn{
    pattern  : parser.parse("Set[lhs_, rhs_]").unwrap(),
    condition: None,
    built_in : Set
  };
  context.set_down_value_attribute("Set", value, read_only_attributes);

  // UpSet[lhs_, rhs_]
  let value = SymbolValue::BuiltIn{
    pattern  : parser.parse("UpSet[lhs_, rhs_]").unwrap(),
    condition: None,
    built_in : UpSet
  };
  context.set_down_value_attribute("UpSet", value, read_only_attributes);

  // endregion

  // region Numeric Computation

  // Numeric Floating Point Conversion
  // N[e_Integer]:=e_Real
  let value = SymbolValue::BuiltIn{
    pattern  : parser.parse("N[e_]").unwrap(),
    condition: None,
    built_in : N
  };
  let mut attributes = read_only_attributes;
  attributes.set(Attribute::Listable);
  context.set_down_value_attribute("N", value, attributes);

  // Plus[exp___]
  let value = SymbolValue::BuiltIn{
    pattern  : parser.parse("Plus[e___]").unwrap(),
    condition: None,
    built_in : Plus
  };
  let mut attributes = read_only_attributes;
  attributes.set(Attribute::Associative);
  attributes.set(Attribute::Commutative);
  attributes.set(Attribute::Variadic);
  attributes.set(Attribute::OneIdentity);
  context.set_down_value_attribute("Plus", value, attributes);

  // Times[exp___]
  let value = SymbolValue::BuiltIn{
    pattern  : parser.parse("Times[e___]").unwrap(),
    condition: None,
    built_in : Times
  };
  let mut attributes = read_only_attributes;
  attributes.set(Attribute::Associative);
  attributes.set(Attribute::Commutative);
  attributes.set(Attribute::Variadic);
  attributes.set(Attribute::OneIdentity);
  context.set_down_value_attribute("Times", value, attributes);

  // endregion

  // region Constants

  // Numeric up_values for Pi`
  { // Scope for pi_record
    let mut pi_record = context.get_symbol("Pi");
    let f = Function::with_symbolic_head("UpSet");
    let value = SymbolValue::Definitions {
      def: Rc::new(f.into()),
      lhs: parser.parse("N[n_]").unwrap(),
      rhs: Rc::new(Real(std::f64::consts::PI).into()),
      condition: None,
    };
    pi_record.up_values.push(value);
    pi_record.attributes = read_only_attributes;;
  }

  // endregion

}

// region utilities

/// The `pattern_function` must be a function`. Finds all symbols or symbols that are heads of functions that are
/// arguments to the given function.
fn collect_symbol_or_head_symbol(pattern_function: Atom) -> Vec<Atom>{
  let f = Function::unwrap(pattern_function.as_ref());
  f.children.iter().filter_map(|c| {
    match c.as_ref() {
      Expression::Symbol(_) => Some(c.clone()),
      Expression::Function(f)=> Some(f.head.clone()),
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
