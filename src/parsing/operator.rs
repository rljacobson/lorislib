/*!

Operators have a variety of properties that affect how they are parsed, interpreted, and evaluated. This module
defines an API to interact with a database of information about operators that can be queried by the various
subsystems needing this information. In also implements a minimalist "database" backend essentially consisting of a
hashmap or two.

An operator is a syntactic component of an expression grammar that may take arguments. The
`Operator` struct holds syntactic data about the operator, which is used by the generic Pratt
parsing algorithm.

A table of operators will hold the operator database for all the operators in the expression
grammar. The parsing algorithm will look up a given operator using the operator's token ("sigil").
Thus, the `OperatorTable` is a `HashMap` from `String` to `Operator`.

*/
#![allow(dead_code)]

use std::collections::HashMap;
use crate::interner::{interned_static, InternedString};


#[allow(unused_imports)]
use crate::logging::{
  Channel,
  log,
  set_verbosity
};


pub struct OperatorTables{
  pub(crate) left: OperatorTable,
  pub(crate) null: OperatorTable
}


/// An operator has a set of properties that determine how it is parsed. Other properties like commutativity that do
/// not affect how an expression is parsed are not associated with the operator but rather with the function the
/// operator is interpreted as.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Operator {
  /// A placeholder for a leaf, such as a literal or symbol.
  NullaryLeaf{
    name: InternedString,
    precedence: i32,
    associativity: Associativity
  },

  /// Binary parenthesizing: `a[[i]]`, `f[a, b, c, …]`
  /// Use for indexing into arrays or function calls.
  /// Note: In this implementation, the head is required, but the parenthesized part is variadic, leaving validation
  /// of arguments to be done by the resulting function expression it parses into.
  Indexing{
    name: InternedString,
    precedence: i32,
    associativity: Associativity,
    l_token: InternedString,
    o_token: InternedString
  },

  /// The most common type: `a+b`, `xy`
  BinaryInfix{
    name: InternedString,
    precedence: i32,
    /// If the associativity is "Full", the operator is chaining.
    /// Chaining means automatically flattening, e.g. `a + b + c` -> `Plus[a, b, c]` instead of `Plus[a, Plus[b, c]]`.
    associativity: Associativity,
    l_token: InternedString
  },

  /// Unary minus or boolean NOT.
  Prefix{
    name: InternedString,
    precedence: i32,
    n_token: InternedString
  },

  /// Postfix: `4!`
  Postfix{
    name: InternedString,
    precedence: i32,
    l_token: InternedString
  },

  /// Operators with a parenthesized middle argument: `a?b:c`.
  /// Note: In this implementation, we allow the middle argument to be empty.
  Ternary{
    name: InternedString,
    precedence: i32,
    associativity: Associativity,
    l_token: InternedString,
    o_token: InternedString
  },

  /// Operators with an optional "tail": `a:=b/;c`, where the `/;c` can optionally be left off, `a:=b`.
  /// In this implementation, the `b` expression cannot be empty.
  OptionalTernary{
    name: InternedString,
    precedence: i32,
    associativity: Associativity,
    l_token: InternedString,
    /// The token present in the optional form.
    o_token: InternedString
  },

  /// Parenthesizing operators: `(exp)`, `| -42 |`, `{a, c, b, …}`
  /// This implementation is variadic, leaving validation of arguments to be done by the resulting function expression.
  /// An alternative implementation could have an arity attribute or an arity range attribute.
  Matchfix{
    name: InternedString,
    precedence: i32, // ignored
    n_token: InternedString,
    o_token: InternedString,
  },

  /*
  // Parses the unusual case of the range operator, which can be any of `a;;b;;c`, `;;b;;c`, `;; ;;c`, `;;b;;`, etc.
  ZeroOrOneTernary{
    name: InternedString,
    precedence: i32,
    // In our only use case, the same token `;;` plays the role of Left, Null, and Other token.
    l_token: InternedString,
    n_token: InternedString,
    o_token: InternedString,
  }
*/
  /*
  Other types of operators not included here are possible. For example:
    * Nullary: leaves, e.g. `Null`, `ø`. We choose to not consider these operators.
    * Quaternary: `a<|b|c|>d`
    * MatchfixBinary: `<|x|y|>` (Dirac's Bra-Ket notation)
    * MatchfixTernary: `<x:y:z>`
  */
}

#[derive(Clone, Debug,  Default)]
pub struct OperatorTable {
  map: HashMap < InternedString, Operator >,
}

impl OperatorTable {

  pub fn new() -> OperatorTable {
    OperatorTable::default()
  }


  /// If `token` has a record in the operator table, return it. Otherwise, return `None`.
  pub fn look_up(&self, token: InternedString) -> Option<&Operator> {
    self.map.get(&token)
  }

  pub fn insert(&mut self, name: InternedString, operator: Operator) {
    self.map.insert(name, operator);
  }

}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Associativity {
  Null,  // Things like constants or identifiers that have no affix or associativity. Also,
         // matchfix operators.
  Non,   // The operator cannot be adjacent to another operator of the same precedence.
  Right, // E.g. 2^3^4 == 2^(3^4) != (2^3)^4
  Left,  // E.g. 3-4-5 == (3-4)-5 != 3 - (4-5)
  Full   // Adjacent operators collapse into a single variadic function,
         // e.g. 1 + 2 + 3 + 4 == Plus(1, 2, 3, 4)
}

impl Associativity{
  pub fn from_str(s: &str) -> Associativity {
    match s {

      "R" => Associativity::Right,

      "L" => Associativity::Left,

      "F" => Associativity::Full,

      "N" => Associativity::Non,

      "" => Associativity::Null,

      anything => {
        eprint!("Unreachable associativity: {}", anything);
        unreachable!()
      }
    }
  }
}

impl Operator {

  pub fn nullary_leaf() -> Self {
    Operator::NullaryLeaf {
      name: interned_static("None"),
      precedence: 0,
      associativity: Associativity::Null
    }
  }

  pub fn name(&self) -> InternedString{
    match self {
      | Operator::NullaryLeaf { name, .. }
      | Operator::Indexing { name, .. }
      | Operator::BinaryInfix { name, .. }
      | Operator::Prefix { name, .. }
      | Operator::Postfix { name, .. }
      | Operator::Ternary { name, .. }
      | Operator::OptionalTernary { name, .. }
      | Operator::Matchfix { name, .. } => {
        *name
      }
    }
  }

  pub fn left_binding_power(&self) -> i32 {
    match self {
      | Operator::NullaryLeaf { precedence, .. }
      | Operator::Indexing { precedence, .. }
      | Operator::BinaryInfix { precedence, .. }
      | Operator::Prefix { precedence, .. }
      | Operator::Postfix { precedence, .. }
      | Operator::Ternary { precedence, .. }
      | Operator::OptionalTernary { precedence, .. }
      | Operator::Matchfix { precedence, .. } => *precedence
    }
  }

  /// Right binding power is computed from precedence and associativity.
  pub fn right_binding_power(&self) -> i32 {
    match self.associativity() {

      | Associativity::Left
      | Associativity::Non => self.left_binding_power() + 1,

      Associativity::Right => self.left_binding_power(),

      // Fully associative means "chaining".
      Associativity::Full  => self.left_binding_power() - 1,

      Associativity::Null  => -1 // Technically, Matchfix is N/A.

    }

  }

  /// This property would be recorded for each operator type if the operator types themselves are to be read in from
  /// a database dynamically.
  pub fn associativity(&self) -> Associativity {
    match self {

      | Operator::BinaryInfix { associativity, .. }
      | Operator::Ternary { associativity, .. }
      | Operator::OptionalTernary { associativity, .. }
          => *associativity,

      // Even though associativity is meaningless for prefix operators, setting their associativity to right causes
      // their right binding power to be their precedence as required.
      Operator::Prefix { .. } => Associativity::Right,

        // Setting Postfix's associativity to null makes its right binding power -1, preventing it from taking an
        // expression on the RHS.
      | Operator::Postfix { .. }
      // Indexing acts like an infix operator on the left and a postfix operator on the right.
      | Operator::Indexing { .. }
      | Operator::Matchfix { .. }
      | Operator::NullaryLeaf { .. }  => Associativity::Null,
    }
  }

  pub fn l_token(&self) -> Option<InternedString> {
    match self {
      | Operator::Indexing { l_token, .. }
      | Operator::BinaryInfix { l_token, .. }
      | Operator::Ternary { l_token, .. }
      | Operator::Postfix { l_token, .. }
      | Operator::OptionalTernary { l_token, .. }
        => Some(*l_token),

      | Operator::Prefix { .. }
      | Operator::Matchfix { .. }
      | Operator::NullaryLeaf { .. }
        => None
    }
  }

  pub fn n_token(&self) -> Option<InternedString> {
    match self {
      | Operator::Prefix { n_token, .. }
      | Operator::Matchfix { n_token, .. }
        => Some(*n_token),

      | Operator::NullaryLeaf { .. }
      | Operator::Indexing { .. }
      | Operator::BinaryInfix { .. }
      | Operator::Postfix { .. }
      | Operator::Ternary { .. }
      | Operator::OptionalTernary { .. }
        => None
    }
  }

  pub fn o_token(&self) -> Option<InternedString> {
    match self {
      | Operator::Indexing { o_token, .. }
      | Operator::Ternary { o_token, .. }
      | Operator::OptionalTernary { o_token, .. }
      | Operator::Matchfix { o_token, .. }
        => Some(*o_token),

      | Operator::NullaryLeaf { .. }
      | Operator::BinaryInfix { .. }
      | Operator::Prefix { .. }
      | Operator::Postfix { .. }
        => None
    }
  }

  // The parse-time functionality of `Operator` lives in the `impl Parser`.
}

// Todo: have this read from an external database.
/// Read in a list of operators and their syntactic properties and generate a `left_operator_table` and
/// `null_operator_table` for use in parsing.
pub(crate) fn get_operator_tables() -> OperatorTables {
  #[allow(non_snake_case)]
  let OPERATORS: &[Operator] = &[

    Operator::Postfix {
      /// The labels `IntoBlank` and friends are "fixed up" at parse time into the more complicated expression
      /// `Pattern[name, Blank[]]`. Thus, `IntoBlank` is a placeholder function for compatibility with the simple
      /// scheme of one operator == one function.
      name: interned_static("IntoBlankNullSequence"),
      precedence: 160,
      l_token: interned_static("___"),
    },

    Operator::Postfix {
      /// See comments on `BlankNullSequence`/`IntoBlankNullSequence`
      name: interned_static("IntoBlankSequence"),
      precedence: 160,
      l_token: interned_static("__"),
    },

    Operator::Postfix {
      /// See comments on `BlankNullSequence`/`IntoBlankNullSequence`
      name: interned_static("IntoBlank"),
      precedence: 160,
      l_token: interned_static("_"),
    },

    Operator::Indexing {
      name: interned_static("Part"),
      precedence: 160,
      associativity: Associativity::Left,
      l_token: interned_static("[["),
      o_token: interned_static("]]"),
    },

    Operator::Indexing {
      name: interned_static("Construct"),
      precedence: 160,
      associativity: Associativity::Null,
      l_token: interned_static("["),
      o_token: interned_static("]"),
    },

    Operator::BinaryInfix {
      name: interned_static("Power"),
      precedence: 150,
      associativity: Associativity::Right,
      l_token: interned_static("^")
    },

    // Unary Minus
    Operator::Prefix {
      name: interned_static("Minus"),
      precedence: 140,
      n_token: interned_static("-")
    },

    Operator::BinaryInfix {
      name: interned_static("Times"),
      precedence: 130,
      associativity: Associativity::Full,
      l_token: interned_static("*")
    },

    Operator::BinaryInfix {
      name: interned_static("Divide"),
      precedence: 130,
      associativity: Associativity::Left,
      l_token: interned_static("/")
    },

    Operator::BinaryInfix {
      name: interned_static("Subtract"),
      precedence: 120,
      associativity: Associativity::Left,
      l_token: interned_static("-")
    },

    Operator::BinaryInfix {
      name: interned_static("Plus"),
      precedence: 110,
      associativity: Associativity::Full,
      l_token: interned_static("+")
    },

    Operator::BinaryInfix {
      name: interned_static("And"),
      precedence: 100,
      associativity: Associativity::Full,
      l_token: interned_static("&&"),
    },

    // Todo: This doesn't parse correctly.
    Operator::BinaryInfix {
      name: interned_static("Or"),
      precedence: 95,
      associativity: Associativity::Full,
      l_token: interned_static("||"),
    },

    // (* Returns `True` if lhs is identical to rhs, `False` otherwise. *)
    Operator::BinaryInfix {
      name: interned_static("SameQ"),
      precedence: 90,
      associativity: Associativity::Non,
      l_token: interned_static("==="),
    },


    // (* Returns `True` if lhs is identical to rhs. *)
    Operator::BinaryInfix {
      name: interned_static("Equal"),
      precedence: 90,
      associativity: Associativity::Non,
      l_token: interned_static("=="),
    },

    // Because Mathematica doesn't use optional ternary operators for conditional *Set, it is convenient for us not
    // to as well. Instead, `exp1 ^= exp2 /; exp3` means `UpSet[exp1, Condition[exp2, exp3]]`
    /*
    Operator::OptionalTernary {
      name: interned_static("Set"),
      precedence: 80,
      associativity: Associativity::Right,
      l_token: interned_static("="),
      o_token: interned_static("/;")
    },

    Operator::OptionalTernary {
      name: interned_static("UpSet"),
      precedence: 80,
      associativity: Associativity::Right,
      l_token: interned_static("^="),
      o_token: interned_static("/;")
    },

    Operator::OptionalTernary {
      name: interned_static("SetDelayed"),
      precedence: 80,
      associativity: Associativity::Right,
      l_token: interned_static(":="),
      o_token: interned_static("/;")
    },

    Operator::OptionalTernary {
      name: interned_static("UpSetDelayed"),
      precedence: 80,
      associativity: Associativity::Right,
      l_token: interned_static("^:="),
      o_token: interned_static("/;")
    },
    */

    Operator::BinaryInfix {
      name: interned_static("Condition"),
      precedence: 85, // Higher precedence than `*Set`
      associativity: Associativity::Left,  // Todo: Associativity of `Condition`?
      l_token: interned_static("/;"),
    },

    Operator::BinaryInfix {
      name: interned_static("RuleDelayed"),
      precedence: 84, // Higher precedence than `*Set`, lower than `Condition`
      associativity: Associativity::Right,
      l_token: interned_static(":>")
    },

    Operator::BinaryInfix {
      name: interned_static("Rule"),
      precedence: 84, // Higher precedence than `*Set`, lower than `Condition`
      associativity: Associativity::Right,
      l_token: interned_static("->")
    },

    Operator::BinaryInfix {
      name: interned_static("ReplaceAll"),
      precedence: 83, // Higher precedence than `*Set`, lower than `Condition`
      associativity: Associativity::Right,
      l_token: interned_static("/.")
    },

    Operator::BinaryInfix {
      name: interned_static("Set"),
      precedence: 80,
      associativity: Associativity::Right,
      l_token: interned_static("=")
    },

    Operator::BinaryInfix {
      name: interned_static("UpSet"),
      precedence: 80,
      associativity: Associativity::Right,
      l_token: interned_static("^="),
    },

    Operator::BinaryInfix {
      name: interned_static("SetDelayed"),
      precedence: 80,
      associativity: Associativity::Right,
      l_token: interned_static(":="),
    },

    Operator::BinaryInfix {
      name: interned_static("UpSetDelayed"),
      precedence: 80,
      associativity: Associativity::Right,
      l_token: interned_static("^:="),
    },

    Operator::BinaryInfix {
      name: interned_static("Unset"),
      precedence: 80,
      associativity: Associativity::Non,
      l_token: interned_static("=."),
    },

    Operator::BinaryInfix {
      name: interned_static("Sequence"),
      precedence: 60,
      associativity: Associativity::Full,
      l_token: interned_static(",")
    },

    Operator::BinaryInfix {
      name: interned_static("CompoundExpression"),
      precedence: 50,
      associativity: Associativity::Full, // Chaining.
      l_token: interned_static(";")
    },

    Operator::Matchfix {
      // A sequence of one expression will automatically be spliced into its parent.
      name: interned_static("Sequence"),
      precedence: 10,
      n_token: interned_static("("),
      o_token: interned_static(")")
    },

    Operator::Matchfix {
      name: interned_static("List"),
      precedence: 10,
      n_token: interned_static("{"),
      o_token: interned_static("}")
    },
  ];

  /*
  // Print a list of op tokens.
  for op in OPERATORS.iter(){
    if let Some(s) = op.l_token(){
      println!("\"{}\", //  {}", resolve_str(s), resolve_str(op.name()));
    }
    if let Some(s) = op.n_token(){
      println!("\"{}\", //  {}", resolve_str(s), resolve_str(op.name()));
    }
    if let Some(s) = op.o_token(){
      println!("\"{}\", //  {}", resolve_str(s), resolve_str(op.name()));
    }
  }
  */

  let mut n_command_table = OperatorTable::new();
  for op in OPERATORS.iter().filter(|op| op.n_token().is_some()) {
    n_command_table.insert(op.n_token().unwrap(), *op);
  }

  let mut l_command_table = OperatorTable::new();
  for op in OPERATORS.iter().filter(|op| op.l_token().is_some()) {
    l_command_table.insert(op.l_token().unwrap(), *op);
  }

  OperatorTables{
    left: l_command_table,
    null: n_command_table
  }
}
