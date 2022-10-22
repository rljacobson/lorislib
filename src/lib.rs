#![feature(type_alias_impl_trait)]
#![allow(dead_code)]

#[macro_use]
mod atom;
mod attributes;
mod context;
mod evaluate;
#[macro_use]
mod format;
mod interner;
mod matching;
mod normal_form;
mod parsing;
pub mod logging;
mod built_ins;

pub use context::Context;
pub use evaluate::evaluate;
pub use parsing::parse;


#[cfg(test)]
mod tests {
  // use super::*;

  #[test]
  fn it_works() {
    let result = 2 + 2;
    assert_eq!(result, 4);
  }
}
