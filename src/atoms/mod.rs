pub mod function;
pub mod sequence_variable;
pub mod sequence;
pub mod symbol;
pub mod variable;
pub mod literal;

use crate::expression::Expression;
use crate::format::Formattable;
use crate::normal_form::NormalFormOrder;

pub use function::Function;
pub use sequence_variable::SequenceVariable;
pub use sequence::Sequence;
pub use symbol::Symbol;
pub use variable::Variable;
pub use literal::Literal;

pub trait Atom: Formattable + NormalFormOrder + Into<Expression> {

  fn deep_copy(&self) -> Expression {
    self.clone().to_expression()
  }

  /// The hash of the expression
  fn hash(&mut self) -> u64;

  /// Wrap self in `Expression`.
  fn to_expression(self) -> Expression {
    self.into()
  }

}
