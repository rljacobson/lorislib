/*!

A `Context` is a namespace. A `Context` struct is a symbol table that holds the values, definitions, and attributes
for symbols within a context.

A lot of things need access to the `Context` in order to read `*Values` or function attributes or for RW access
during evaluation. The codebase is transitioning to a `Context` model of shared mutable state via interior
mutability.

Todo: Predefined and built-in symbols should live in the `Std` context. Contexts should be able to define
      visibility and other finer-grained access controls, like read-only attributes, etc. In other words, make
      `Context`s modules.

*/
#![allow(dead_code)]


use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

use crate::{atom::{
  Atom
}, attributes::{
  Attributes,
  Attribute
}, built_ins::{
  BuiltinFn,
  register_builtins
}};
use crate::interner::{interned_static, InternedString, resolve_str};
use crate::logging::set_verbosity;
// use crate::parsing::{Lexer, parse};


pub struct Context{
  // todo: Should there be a context path object?
  name   : InternedString,
  symbols: HashMap<InternedString, SymbolRecord>,
  state: u64
}

impl Context {

  pub fn new_global_context() -> Context {
    let mut context = Context{
      name: interned_static("Global"),
      symbols: HashMap::new(),
      /// Incremented every time this context is modified. It is accessed publicly by `state_version` and used during
      /// evaluation to determine if an expression is completely evaluated.
      state: 0
    };

    register_builtins(&mut context);
    context.set_verbosity(1);
    context
  }

  /// Used for testing and debugging to avoid calling `register_builtins`.
  pub(crate) fn without_built_ins(name: InternedString) -> Context {
    Context{
      name,
      symbols: HashMap::new(),
      state: 0
    }
  }

  // region Getters and Setters

  pub fn state_version(&self) -> u64 {
    self.state
  }

  /// Sets the logging verbosity, the level at which messages are reported to the user.
  // todo: Make this an actual variable in the context instead of a global.
  pub fn set_verbosity(&mut self, verbosity: i32) {
    set_verbosity(verbosity)
  }

  pub fn get_attributes(&self, symbol: InternedString) -> Attributes {
    match self.symbols.get(&symbol) {
      None => Attributes::default(),

      Some(record) => record.attributes
    }
  }

  pub fn get_symbol(&self, symbol: InternedString) ->  Option<&SymbolRecord> {
    self.symbols.get(&symbol)
  }

  pub fn get_symbol_mut(&mut self, symbol: InternedString) ->  &mut SymbolRecord {
    self.symbols.entry(symbol).or_insert_with(
      | | {
        SymbolRecord::new(symbol)
      }
    )
  }

  /// This method does not check for read-only! Only use for registering built-ins.
  pub(crate) fn set_down_value_attribute(&mut self, symbol: InternedString, value: SymbolValue, attributes: Attributes) {
    let record = self.get_symbol_mut(symbol);

    if !record.down_values.contains(&value) {
      record.down_values.push(value);
    }
    record.attributes.update(attributes);
  }


  pub fn set_attributes(&mut self, symbol: InternedString, attributes: Attributes) -> Result<(), String> {
    {
      let record = self.get_symbol_mut(symbol);

      // Todo: Fix enforcement of read/write-protection.
      // if record.attributes.attributes_read_only() {
      //   Err(format!("Symbol {} has read-only attributes", resolve_str(symbol)))
      // } else {
      record.attributes.update(attributes);
      Ok(())
      // }
    }
  }

  // todo: We should only have `set_attributes(…)` since `Attribute` implements `Into<Attributes>`.
  pub fn set_attribute(&mut self, symbol: InternedString, attribute: Attribute) -> Result<(), String> {
    self.set_attributes(symbol, attribute.into())
  }

  pub fn set_down_value(&mut self, symbol: InternedString, value: SymbolValue) -> Result<(), String> {
    let record = self.get_symbol_mut(symbol);
    if record.down_values.contains(&value) {
      return Ok(());
    }

    // if record.attributes.read_only() {
    //   Err(format!("Symbol {} is read-only", resolve_str(symbol)))
    // } else {
      record.down_values.push(value);
      self.state += 1;
      Ok(())
    // }
  }


  pub fn set_display_function(&mut self, symbol: InternedString, value: SymbolValue) -> Result<(), String> {
    let record = self.get_symbol_mut(symbol);

    // if record.attributes.read_only() {
    //   Err(format!("Symbol {} is read-only", resolve_str(symbol)))
    // } else {
      record.down_values.push(value);
      self.state += 1;
      Ok(())
    // }
  }

  pub fn set_up_value(&mut self, symbol: InternedString, value: SymbolValue) -> Result<(), String> {
    let record = self.get_symbol_mut(symbol);
    if record.up_values.contains(&value) {
      return Ok(());
    }

    // if record.attributes.read_only() {
    //   Err(format!("Symbol {} is read-only", resolve_str(symbol)))
    // } else {
      record.up_values.push(value);
      self.state += 1;
      Ok(())
    // }
  }

  pub fn set_own_value(&mut self, symbol: InternedString, value: SymbolValue) -> Result<(), String> {
    let record = self.get_symbol_mut(symbol);
    if record.own_values.contains(&value) {
      return Ok(());
    }

    // if record.attributes.read_only() {
    //   Err(format!("Symbol {} is read-only", resolve_str(symbol)))
    // } else {
      record.own_values.push(value);
      self.state += 1;
      Ok(())
    // }
  }

  pub fn set_sub_value(&mut self, symbol: InternedString, value: SymbolValue) -> Result<(), String> {
    let record = self.get_symbol_mut(symbol);
    if record.sub_values.contains(&value) {
      return Ok(());
    }

    // if record.attributes.read_only() {
    //   Err(format!("Symbol {} is read-only", resolve_str(symbol)))
    // } else {
      record.sub_values.push(value);
      self.state += 1;
      Ok(())
    // }
  }

  // todo: Not especially efficient if the symbol was never defined.
  // todo: Should clearing a symbol increment the state version? No for now.
  pub fn clear_symbol(&mut self, symbol: InternedString) -> Result<(), String> {
    { // Scope for record
      let record = self.get_symbol_mut(symbol);
      if record.attributes.read_only() || record.attributes.protected() {
        return Err(format!("Symbol {} is read-only", resolve_str(symbol)))
      }
    }
    self.symbols.remove(&symbol);
    Ok(())
  }
/*
  pub fn get_up_values(&self, symbol: InternedString) -> Option<Vec<SymbolValue>> {
    match self.symbols[symbol] {
      None => None,
      Some(record) => {
        // todo: get rid of this clone.
        Some(record.UpValues.clone())
      }
    }
  }
  */
/*
  pub fn get_own_values(&self, symbol: InternedString) -> Option<Vec<SymbolValue>> {
    match self.symbols[symbol] {
      None => None,
      Some(record) => {
        // todo: get rid of this clone.
        Some(record.OwnValues.clone())
      }
    }
  }
*/

  // endregion

}

/// Used to communicate across function calls
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ContextValueStore {
  OwnValues,
  UpValues,
  DownValues,
  SubValues,
  NValues,
  DisplayFunction,
}

// todo: Should `SymbolRecord` store `Rc<SymbolValue>`s? These are all basicly read-only, because the vector is
//       usually wiped for re-definitions.
pub struct SymbolRecord {
  pub symbol: InternedString,
  pub attributes: Attributes,

  /// OwnValues define how the symbol appearing alone should be evaluated. They have the form `x :> expr` or `x=expr`.
  pub own_values: Vec<SymbolValue>,

  /// UpValues define how M-expressions having the symbol as an argument should be evaluated. They typically have the
  /// form `f[pattern,g[pattern],pattern]:>expr`. UpValues are applied before DownValues.
  pub up_values:  Vec<SymbolValue>,

  /// DownValues define how M-expressions having the symbol as their head should be evaluated. They typically have the
  /// form `f[pattern]:>expr`
  pub down_values: Vec<SymbolValue>,

  /// SubValues define how M-expressions having an M-expression with the symbol as a head should be evaluated. They
  /// typically have the form `f[pat][pat]:>exp`.
  pub sub_values: Vec<SymbolValue>,
}

impl SymbolRecord {
  pub fn new(name: InternedString) -> SymbolRecord{
    SymbolRecord {
      symbol: name,
      // Todo: Store attributes separately. They need to be accessed very frequently, very often for symbols that do
      //       not yet exist in the context. Not so much for efficiency as programmer ergonomics.
      attributes: Default::default(),
      own_values: vec![],
      up_values: vec![],
      down_values: vec![],
      sub_values: vec![]
    }
  }
}


/// A `SymbolValue` is a wrapper for `RuleDelayed` used for storing the rule in a symbol table as an own/up/down/sub
/// value. The wrapper provides convenience methods and stores the expression that originally created the value.
#[derive(Clone)]
pub enum SymbolValue{
  Definitions {
    def: Atom, // The original (sub)expression used to create this `SymbolValue`.
    lhs: Atom, // Treated as if wrapped in HoldPattern
    rhs: Atom,
    condition: Option<Atom>,
  },
  BuiltIn {
    pattern  : Atom,
    condition: Option<Atom>,
    built_in : BuiltinFn
  }
}

// Function pointers don't implement `PartialEq`:
//   https://github.com/rust-lang/unsafe-code-guidelines/issues/239
impl PartialEq for SymbolValue {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {

      (
        SymbolValue::BuiltIn {pattern: p1, condition: c1, built_in: _b1},
        SymbolValue::BuiltIn {pattern: p2, condition: c2, built_in: _b2},
      ) => {
        p1==p2 && c1==c2 //&& (b1 as *const _ == b2 as *const _)
      }

      (
        SymbolValue::Definitions { def: d1, .. },
        SymbolValue::Definitions { def: d2, .. }
      ) => {
        // If the original definitions are the same, the rest had better be the same also.
        d1==d2
      }

      _ => false

    }
  }
}

impl Eq for SymbolValue {}

impl Debug for SymbolValue {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {

      SymbolValue::Definitions { def, lhs, rhs, condition } => {
        write!(
          f,
          "SymbolValue::Definitions{{ def: {}, lhs: {}, rhs: {}, condition: {:?}}}",
          def,
          lhs,
          rhs,
          condition
        )
      }

      SymbolValue::BuiltIn { pattern, condition, built_in } => {
        write!(
          f,
          "SymbolValue::Definitions{{ pattern: {}, condition: {:?}, built_in: {:?}}}",
          pattern,
          condition,
          built_in as *const _
        )
      }

    }

  }
}


// Tests
// `Context` is tested in `builltins.rs` and other client code.
