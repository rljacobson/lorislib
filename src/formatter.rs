/*!

  A `Formatter` holds information about how to format an expression, that is, how
  to express the expression as a string. Right now this is a stub
  implementation, but it is convenient to have it in place now, because any
  real application will undoubtedly need to have it.

*/

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
