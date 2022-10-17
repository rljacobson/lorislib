#![feature(type_alias_impl_trait)]
#![allow(dead_code)]

#[macro_use]
mod format;
pub mod expression;
pub mod logging;
mod normal_form;
mod attributes;
mod atom;
mod matching;
mod context;
mod parsing;
mod builtins;
mod evaluate;
mod interner;

pub use evaluate::evaluate;
pub use context::Context;
pub use parsing::{
  parse
};


#[cfg(test)]
mod tests {
  // use super::*;

  #[test]
  fn it_works() {
    let result = 2 + 2;
    assert_eq!(result, 4);
  }
}
