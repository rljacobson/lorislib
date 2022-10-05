/*!

A context is a namespace. A `Context` struct is a symbol table that holds the
values, definitions, and attributes for symbols within a context. It is the
`Context` that owns expressions related to a symbol.

Much of this should arguably be implemented in the language being implemented.
However, doing so would mean that information about the original expression that
created the symbol and its definitions would not be retained.


*/

use std::collections::HashMap;

use crate::{
  expression::Expression,
  attributes::Attributes,
  atoms::Symbol
};

pub struct Context{
  name: String,
  path: String, // todo: Should there be a context path object?
  symbols: HashMap<String, SymbolRecord>
}


pub struct SymbolRecord {
  symbol: Symbol,
  attributes: Attributes,

  /// OwnValues define how the symbol appearing alone should be evaluated. They have the form `x :> expr`.
  own_values: Vec<SymbolValue>,

  /// UpValues define how M-expressions having the symbol as an argument should be evaluated. They typically have the
  /// form `f[pattern,g[pattern],pattern]:>expr`. UpValues are applied before DownValues.
  up_values:  Vec<SymbolValue>,

  /// DownValues define how M-expressions having the symbol as their head should be evaluated. They typically have the
  /// form `f[pattern]:>expr`
  down_values: Vec<SymbolValue>,

  /// SubValues define how M-expressions having an M-expression with the symbol as a head should be evaluated. They
  /// typically have the form `f[pat][pat]:>exp`.
  sub_values: Vec<SymbolValue>,
}


/// A `SymbolValue` is a wrapper for `RuleDelayed` used for storing the rule in a symbol table as an own/up/down/sub
/// value. The wrapper provides convenience methods and stores the expression that originally created the value.
struct SymbolValue{
  def: Expression,  // The original (sub)expression used to create this `SymbolValue`.
  lhs: Expression,  // Treated as if wrapped in HoldPattern
  rhs: Expression   //
}
