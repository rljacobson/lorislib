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
use std::str::FromStr;

use csv::{ReaderBuilder, Trim, StringRecordIter};
use strum_macros::EnumString;

use crate::interner::{interned, interned_static, InternedString};
#[allow(unused_imports)]
use crate::logging::{
  Channel,
  log,
  set_verbosity
};


static OPERATOR_DB_FILE: &str = "lorislib/resources/operators.csv";


pub struct OperatorTables{
  pub(crate) left: OperatorTable,
  pub(crate) null: OperatorTable
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, EnumString)]
pub enum Affix {
  Infix,
  Prefix,
  Postfix,
  Matchfix,
  Null
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

      "R" | "Right" => Associativity::Right,

      "L" | "Left" => Associativity::Left,

      "F" | "Full" => Associativity::Full,

      "N" | "Non" => Associativity::Non,

      "" => Associativity::Null,

      _ => {
        unreachable!("Unreachable associativity: {}", s);
      }
    }
  }
}


/// An operator has a set of properties that determine how it is parsed. Other properties like commutativity that do
/// not affect how an expression is parsed are not associated with the operator but rather with the function the
/// operator is interpreted as.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Operator {

  /// The most common type: `a+b`, `xy`
  BinaryInfix{
    name: InternedString,
    precedence: i32,
    /// If the associativity is "Full", the operator is chaining.
    /// Chaining means automatically flattening, e.g. `a + b + c` -> `Plus[a, b, c]` instead of `Plus[a, Plus[b, c]]`.
    associativity: Associativity,
    l_token: InternedString
  },

  /// The second operand is optional: `s_h`, `s_`.
  BinaryInfixOptional{
    name: InternedString,
    precedence: i32,
    /// If the associativity is "Full", the operator is chaining.
    /// Chaining means automatically flattening, e.g. `a + b + c` -> `Plus[a, b, c]` instead of `Plus[a, Plus[b, c]]`.
    associativity: Associativity,
    l_token: InternedString
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

  /// Same as binary infix, but chains with any other `Inequality` operator.
  Inequality {
    name: InternedString,
    precedence: i32,
    /// Associativity is  always "Full".
    l_token: InternedString
  },

  /// A placeholder for a leaf, such as a literal or symbol, or `_.`
  NullaryLeaf{
    name: InternedString,
    precedence: i32,
    n_token: InternedString
  },

  /// Used only for `#`
  NullaryRepeated {
    name: InternedString,
    precedence: i32,
    n_token: InternedString
  },

  // E.g. `f'''`
  UnaryPostfixRepeated {
    name: InternedString,
    precedence: i32,
    l_token: InternedString
  },

  /// Special case of `;;`
  Span {
    name: InternedString,
    precedence: i32,
    n_token: InternedString,
    l_token: InternedString,
    o_token: InternedString,
  },

  /// The operand is optional: `_h`, `_`
  UnaryPrefixOptional{
    name: InternedString,
    precedence: i32,
    n_token: InternedString
  },

  /// Unary prefix, e.g. minus or boolean NOT.
  UnaryPrefix {
    name: InternedString,
    precedence: i32,
    n_token: InternedString
  },

  /// Postfix: `4!`
  UnaryPostfix {
    name: InternedString,
    precedence: i32,
    l_token: InternedString
  },

  /// Operators with a parenthesized middle argument: `a?b:c`.
  /// Note: In this implementation, we allow the middle argument to be empty.
  TernaryInfix {
    name: InternedString,
    precedence: i32,
    associativity: Associativity,
    l_token: InternedString,
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

  Other types of operators not included here are possible. For example:
    * Nullary: leaves, e.g. `Null`, `ø`. We choose to not consider these operators.
    * Quaternary: `a<|b|c|>d`
    * MatchfixBinary: `<|x|y|>` (Dirac's Bra-Ket notation)
    * MatchfixTernary: `<x:y:z>`
  */
}

impl Operator {

  pub fn nullary_leaf() -> Self {
    Operator::NullaryLeaf {
      name      : interned_static("None"),
      precedence: 0,
      n_token   : interned_static("None")
    }
  }

  pub fn set_precedence(&mut self, mut p: i32)  {
    match self {
      Operator::BinaryInfix {          precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::BinaryInfixOptional {  precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::Indexing {             precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::Inequality {           precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::NullaryLeaf {          precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::NullaryRepeated {      precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::UnaryPostfixRepeated { precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::Span {                 precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::UnaryPrefixOptional {  precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::UnaryPrefix {          precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::UnaryPostfix {         precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::TernaryInfix {         precedence, .. } => { std::mem::swap(precedence, &mut p)}
      Operator::Matchfix {             precedence, .. } => { std::mem::swap(precedence, &mut p)}
    }
  }


  pub fn name(&self) -> InternedString{
    match self {
      | Operator::BinaryInfix {          name, .. }
      | Operator::BinaryInfixOptional {  name, .. }
      | Operator::Indexing {             name, .. }
      | Operator::Inequality {           name, .. }
      | Operator::Matchfix {             name, .. }
      | Operator::NullaryLeaf {          name, .. }
      | Operator::NullaryRepeated {      name, .. }
      | Operator::Span {                 name, .. }
      | Operator::TernaryInfix {         name, .. }
      | Operator::UnaryPostfix {         name, .. }
      | Operator::UnaryPostfixRepeated { name, .. }
      | Operator::UnaryPrefix {          name, .. }
      | Operator::UnaryPrefixOptional {  name, .. }
      => {
        *name
      }
    }
  }

  pub fn left_binding_power(&self) -> i32 {
    match self {
      | Operator::BinaryInfix {          precedence, .. }
      | Operator::BinaryInfixOptional {  precedence, .. }
      | Operator::Indexing {             precedence, .. }
      | Operator::Inequality {           precedence, .. }
      | Operator::Matchfix {             precedence, .. }
      | Operator::NullaryLeaf {          precedence, .. }
      | Operator::NullaryRepeated {      precedence, .. }
      | Operator::Span {                 precedence, .. }
      | Operator::TernaryInfix {         precedence, .. }
      | Operator::UnaryPostfix {         precedence, .. }
      | Operator::UnaryPostfixRepeated { precedence, .. }
      | Operator::UnaryPrefix {          precedence, .. }
      | Operator::UnaryPrefixOptional {  precedence, .. }
      => {
        *precedence
      }
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

      | Operator::BinaryInfix {         associativity, .. }
      | Operator::BinaryInfixOptional { associativity, .. }
      | Operator::Indexing {            associativity,.. }
      | Operator::TernaryInfix {        associativity, .. }
      => *associativity,

      // Even though associativity is meaningless for prefix operators, setting their associativity to right causes
      // their right binding power to be their precedence as required.
      | Operator::UnaryPrefix { .. }
      | Operator::UnaryPrefixOptional { .. }
      => Associativity::Right,

      Operator::Inequality { .. }
      =>  Associativity::Full,

      // Setting Postfix's associativity to null makes its right binding power -1, preventing it from taking an
      // expression on the RHS.
      | Operator::Matchfix { .. }
      | Operator::NullaryLeaf { .. }
      | Operator::NullaryRepeated { .. }
      | Operator::Span { .. }
      | Operator::UnaryPostfix { .. }
      | Operator::UnaryPostfixRepeated { .. }
      => Associativity::Null,
    }
  }

  pub fn l_token(&self) -> Option<InternedString> {
    match self {

      | Operator::BinaryInfix {          l_token, .. }
      | Operator::BinaryInfixOptional {  l_token, .. }
      | Operator::Indexing {             l_token, .. }
      | Operator::Inequality {           l_token, .. }
      | Operator::Span {                 l_token, .. }
      | Operator::TernaryInfix {         l_token, .. }
      | Operator::UnaryPostfix {         l_token, .. }
      | Operator::UnaryPostfixRepeated { l_token,.. }
      => Some(*l_token),

      // | Operator::Matchfix { .. }
      // | Operator::NullaryLeaf { .. }
      // | Operator::NullaryRepeated {.. }
      // | Operator::UnaryPrefix { .. }
      // | Operator::UnaryPrefixOptional { .. }
      _ => None,

    }
  }

  pub fn n_token(&self) -> Option<InternedString> {
    match self {

      | Operator::Matchfix {            n_token, .. }
      | Operator::NullaryLeaf {         n_token, .. }
      | Operator::NullaryRepeated {     n_token,.. }
      | Operator::Span {                n_token, .. }
      | Operator::UnaryPrefix {         n_token, .. }
      | Operator::UnaryPrefixOptional { n_token, .. }
      => Some(*n_token),

      // | Operator::BinaryInfix { .. }
      // | Operator::BinaryInfixOptional { .. }
      // | Operator::Indexing { .. }
      // | Operator::Inequality { .. }
      // | Operator::TernaryInfix { .. }
      // | Operator::UnaryPostfix { .. }
      // | Operator::UnaryPostfixRepeated { .. }
      _ => None,

    }
  }

  pub fn o_token(&self) -> Option<InternedString> {
    match self {

      | Operator::Indexing {     o_token, .. }
      | Operator::Matchfix {     o_token, .. }
      | Operator::Span {         o_token, .. }
      | Operator::TernaryInfix { o_token, .. }
      => Some(*o_token),

      // | Operator::BinaryInfix { .. }
      // | Operator::BinaryInfixOptional { .. }
      // | Operator::Inequality { .. }
      // | Operator::NullaryLeaf { .. }
      // | Operator::NullaryRepeated { .. }
      // | Operator::UnaryPostfix { .. }
      // | Operator::UnaryPostfixRepeated { .. }
      // | Operator::UnaryPrefix { .. }
      // | Operator::UnaryPrefixOptional  { .. }
      _ => None

    }
  }

  // The parse-time functionality of `Operator` lives in the `impl Parser`.
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

//  Internal to module, a convenience container for fields of the operator DB.
struct OperatorRecord<'s> {
  pub name: InternedString,

  pub precedence   : i32,
  pub n_token      : InternedString, //Option<InternedString>,
  pub l_token      : InternedString, //Option<InternedString>,
  pub o_token      : InternedString, //Option<InternedString>,
  pub arity        : i16,
  pub affix        : Affix,
  pub associativity: Associativity,
  pub parselet     : &'s str,
  pub comments     : &'s str,

}

// Todo: have this read from an external database.
/// Read in a list of operators and their syntactic properties and generate a `left_operator_table` and
/// `null_operator_table` for use in parsing.
pub(crate) fn get_operator_tables() -> OperatorTables {
  let mut csv_reader
      = ReaderBuilder::new().delimiter(b',')
                            .has_headers(true)
                            .trim(Trim::All)
                            .from_path(OPERATOR_DB_FILE)
                            .unwrap();

  // let reader = BufReader::new(f);
  let mut l_operator_table = OperatorTable::new();
  let mut o_operator_table = OperatorTable::new();
  let mut n_operator_table = OperatorTable::new();

  // let mut lines = reader.lines();
  // lines.next(); // Eat the column headers
  let records =  csv_reader.records();
  for result in records {
    let record = result.unwrap();
    let mut fields: StringRecordIter = record.iter();

    /*
    COLUMNS
    Name,
    Precedence,
    N Tokens,
    L Tokens,
    O Tokens,
    Arity,
    Affix,
    Associativity,
    Meaningful,
    Parselet,
    Comments,
    */
    let op_record = OperatorRecord {
      name: interned(fields.next().unwrap()),
      precedence: fields.next().unwrap().parse::<i32>().unwrap(),
      l_token : interned(fields.next().unwrap()),
      // l_token   : fields.next().map_or(
      //   None,
      //   |s| if s != "" { Some(interned(s)) } else { None }
      // ),
      n_token : interned(fields.next().unwrap()),
      // n_token   : fields.next().map_or(
      //   None,
      //   |s| if s != "" { Some(interned(s)) } else { None }
      // ),
      o_token : interned(fields.next().unwrap()),
      // o_token   : fields.next().map_or(
      //   None,
      //   |s| if s != "" { Some(interned(s)) } else { None }
      // ),

      arity     : fields.next().unwrap().parse::<i16>().unwrap(),
      affix     : Affix::from_str(fields.next().unwrap()).unwrap(),
      associativity : Associativity::from_str(fields.next().unwrap()),

      parselet  : fields.next().unwrap(),
      comments  : fields.next().unwrap(),
    };

    let new_op: Operator = // the following match
    match op_record.parselet {
      // Only seven of the operator syntax forms appear explicitly. These are the forms that cannot be inferred from
      // the arity and affix.
      "BinaryInfixOptional" => {
        Operator::BinaryInfixOptional {
          name         : op_record.name,
          precedence   : op_record.precedence,
          associativity: op_record.associativity,
          l_token      : op_record.l_token
        }
      }

      "Indexing" => {
        Operator::Indexing{
          name         : op_record.name,
          precedence   : op_record.precedence,
          associativity: op_record.associativity,
          l_token      : op_record.l_token,
          o_token      : op_record.o_token,
        }
      }

      "Inequality" => {
        Operator::Inequality {
          name      : op_record.name,
          precedence: op_record.precedence,
          l_token   : op_record.l_token
        }
      }

      "NullaryRepeated" => {
        Operator::NullaryRepeated {
          name      : op_record.name,
          precedence: op_record.precedence,
          n_token   : op_record.n_token,
        }

      }

      "Span" => {
        Operator::Span {
          name      : op_record.name,
          precedence: op_record.precedence,
          n_token   : op_record.n_token,
          l_token   : op_record.l_token,
          o_token   : op_record.o_token,
        }
      }

      "UnaryPostfixRepeated" => {
        Operator::UnaryPostfixRepeated{
          name      : op_record.name,
          precedence: op_record.precedence,
          l_token   : op_record.n_token,
        }
      }

      "UnaryPrefixOptional" => {
        Operator::UnaryPrefixOptional{
          name      : op_record.name,
          precedence: op_record.precedence,
          n_token   : op_record.n_token,
        }
      }

      _ => {
        // The remaining cases can be inferred from the arity and affix.
        match (op_record.arity, op_record.affix) {
          (2, Affix::Infix) => {
            Operator::BinaryInfix {
              name         : op_record.name,
              precedence   : op_record.precedence,
              associativity: op_record.associativity,
              l_token      : op_record.l_token,
            }
          }

          (_, Affix::Matchfix) => {
            Operator::Matchfix {
              name      : op_record.name,
              precedence: op_record.precedence,
              n_token   : op_record.n_token,
              o_token   : op_record.o_token,
            }
          }

          (1, Affix::Prefix) => {
            Operator::UnaryPrefix {
              name      : op_record.name,
              precedence: op_record.precedence,
              n_token   : op_record.n_token,
            }
          }

          (1, Affix::Postfix) => {
            Operator::UnaryPostfix {
              name      : op_record.name,
              precedence: op_record.precedence,
              l_token   : op_record.l_token,
            }
          }

          (3, Affix::Infix) => {
            Operator::TernaryInfix {
              name         : op_record.name,
              precedence   : op_record.precedence,
              associativity: op_record.associativity,
              l_token      : op_record.l_token,
              o_token      : op_record.o_token
            }
          }

          (0, Affix::Null) => {
            Operator::NullaryLeaf {
              name      : op_record.name,
              precedence: op_record.precedence,
              n_token   : op_record.n_token
            }
          }

          (arity, affix) => {
            log(
              Channel::Error,
              1,
              format!("Unknown (arity, affix) pair: ({}, {:?}), Parselet: {}", arity, affix, op_record.parselet).as_str(),
            );
            continue;
          }

        }
      }
    };

    // log(Channel::Debug, 5, format!("Read from CSV: {:?}", &new_op).as_str());

    if let Some(tok) = &new_op.l_token() {
      l_operator_table.insert(tok.clone(), new_op.clone());
    }
    if let Some(n_token) = &new_op.n_token() {
      let new_op = new_op.clone();
      n_operator_table.insert(n_token.clone(), new_op);
    }

    if let Some(tok) = &new_op.o_token() {
      let mut new_op = new_op.clone();
      new_op.set_precedence(-2);
      o_operator_table.insert(tok.clone(), new_op);
    }
  }


  OperatorTables{
    left: l_operator_table,
    null: n_operator_table
  }
}
