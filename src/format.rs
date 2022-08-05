/*!

  A `Formatter` holds information about how to format an expression, that is, how
  to express the expression as a string. Right now this is a stub
  implementation, but it is convenient to have it in place now, because any
  real application will undoubtedly need to have it.

  "Formatting" needs to be distinct from Rust's standard `Display` trait, because
  expressions are (potentially) formatted differently depending on the context. for
  example, there might be different formats, such as a LaTeX format, a human-readable
  UTF-8 string format, and an M-expression format. Or an expression might dictate the
  format of its child expressions. Unfortunately, even though Rust's `Display` trait
  works the same way as this module does, passing state around with a `Format` struct,
  there is no way to make it work with a different set of formatting rules.

*/

use std::fmt::Display;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Formatter {
  /* pass */
}

impl Default for Formatter {
    fn default() -> Self {
        Self {  }
    }
}


pub trait Formatable {
  fn format(&self, formatter: &Formatter) -> String;
}

macro_rules! display_formatable_impl {
  ($type_name:ty) => {
    impl std::fmt::Display for $type_name {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format(&Formatter::default()))
      }
    }
  }
}


impl Display for Formatter {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "Formatter")
  }
}
