#![feature(type_alias_impl_trait)]
#![feature(impl_trait_in_assoc_type)]
#![allow(dead_code)]
/*

ToDo: Since we link to the log (v0.4.17) crate anyway, we should use it. Look at flexi_logger:
      https://docs.rs/flexi_logger/0.24.0/flexi_logger/filter/index.html

*/
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
pub use format::{DisplayForm, ExpressionFormatter, Formattable};


#[cfg(test)]
mod tests {
  // use super::*;

  #[test]
  fn it_works() {
    let result = 2 + 2;
    assert_eq!(result, 4);
  }
}
