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
use std::borrow::Cow;

use strum::EnumString;


#[derive(Copy, Clone, Debug, PartialEq, Eq, EnumString, Hash)]
pub enum DisplayForm {
  #[strum(serialize = "Std`InputForm")]
  Input,
  #[strum(serialize = "Std`FullForm")]
  Full,
  #[strum(serialize = "Std`TraditionalForm")]
  Traditional,
  #[strum(serialize = "Std`TeXForm")]
  TeX,
  #[strum(serialize = "Std`StandardForm")]
  Standard,
  #[strum(serialize = "Std`OutputForm")]
  Output,
  #[strum(serialize = "Std`MatcherForm")]
  Matcher,

}

impl Default for DisplayForm {
  fn default() -> DisplayForm {
    DisplayForm::Input
  }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
/// Parameters used in methods that transform expressions into strings.
// Todo: This will probably need to include context at some point.
pub struct ExpressionFormatter {
  pub form: DisplayForm,
}

static DEFAULT_FORMATTER: Cow<ExpressionFormatter> = Cow::Owned(ExpressionFormatter {
  form: DisplayForm::Input
});

impl ExpressionFormatter {
  pub fn default() -> Cow<'static, ExpressionFormatter> {
    DEFAULT_FORMATTER.clone()
  }
}

impl From<DisplayForm> for ExpressionFormatter {
  fn from(form: DisplayForm) -> Self {
    ExpressionFormatter {
      form
    }
  }
}

pub trait Formattable {
  fn format(&self, formatter: &ExpressionFormatter) -> String;
}


macro_rules! display_formattable_impl {
  ($type_name:ty) => {
    impl std::fmt::Display for $type_name
        where $type_name: Formattable
    {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let expression_formatter = ExpressionFormatter::default().clone();
        write!(f, "{}", self.format(&expression_formatter))
      }
    }
  }
}

pub(crate) use display_formattable_impl;
