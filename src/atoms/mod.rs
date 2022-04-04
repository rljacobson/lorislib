pub mod function;
pub mod sequence_variable;
pub mod sequence;
pub mod symbol;
pub mod variable;
pub mod literal;

use crate::expression::Expression;
use crate::format::Formatable;
use crate::normal_form::NormalFormOrder;

pub use function::Function;
pub use sequence_variable::SequenceVariable;
pub use sequence::Sequence;
pub use symbol::Symbol;
pub use variable::Variable;
pub use literal::Literal;

pub trait Atom: Formatable+NormalFormOrder+Into<Expression> {

  fn as_expression(self) -> Expression {
    self.into()
  }

}
