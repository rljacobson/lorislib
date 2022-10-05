/*!

An `Atom` is the smallest unit of an expression that:

  * needs to have the responsibility of hashing itself
  * needs to have the responsibility of displaying itself
  * needs to have the responsibility of deep-copying itself
  * forms an equivalence class with all other things to which it can be compared

`Atom`s are the natural units with those responsibilities. They can we thought of as the units responsible
for providing structure to expressions. We also include the `SequenceVariable` and `Variable` as `Atom`s.

We cannot just use `dyn Atom` everywhere, because `Atom` cannot be a trait object as it's not `Sized`. Nor do we want
to implement each `Atom` as a variant in a single enum. Instead, we wrap things that implement `Atom` in an enum,
namely the `Expression` enum, keeping their implementations separate. The downside is that `Expression` needs to be
kept in sync with whatever `Atom`s exist. As a bonus, `Expression` is a concrete type for which we can provide a
blanket implementation of `Hash`, for example.

*/

mod function;
mod sequence_variable;
mod sequence;
mod symbol;
mod variable;
mod string_literal;
mod integer;
mod real;

use crate::expression::Expression;
use crate::format::Formattable;
use crate::normal_form::NormalFormOrder;

pub use function::Function;
pub use sequence_variable::SequenceVariable;
pub use sequence::Sequence;
pub use symbol::Symbol;
pub use variable::Variable;
pub use string_literal::StringLiteral;
pub use integer::Integer;
pub use real::Real;

pub trait Atom: Clone + Formattable + NormalFormOrder + Into<Expression> {

  fn deep_copy(&self) -> Expression {
    // todo: This is not a deep copy.
    self.clone().to_expression()
  }

  /// The hash of the `Atom`
  /**
  If two expressions just happen to have the same representation, a string and a symbol, we still want their hashes
  to differ. So we hash a type-specific prefix before hashing the data. We use the same prefix as Cory's expreduce
  for compatibility. Some of the atoms in expreduce don't exist in loris, and some of our atoms don't exist in
  expreduce. I believe Cory chose his prefixes at random. We do the same.

  expreduce

      real      : [195, 244, 76 , 249, 227, 115, 88 , 251]
      complex   : [82 , 226, 223, 39 , 113, 26 , 149, 249]
      expression: [72 , 5  , 244, 86 , 5  , 210, 69 , 30]
      integer   : [242, 99 , 84 , 113, 102, 46 , 118, 94]
      rational  : [90 , 82 , 214, 51 , 52 , 7  , 7  , 33]
      string    : [102, 206, 57 , 172, 207, 100, 198, 133]
      symbol    : [107, 10 , 247, 23 , 33 , 221, 163, 156]

  Loris

      function         : [1, 207, 143, 106, 203, 58, 96, 148]
      sequence         : [174, 52 , 210, 181, 122, 46 , 205, 101]
      sequence_variable: [57 , 129, 46 , 235, 112, 49 , 134, 6]
      variable         : [5  , 15 , 105, 181, 241, 116, 76 , 166]

   */
  fn hash(&self) -> u64;

  /// Wrap self in `Expression`.
  fn to_expression(self) -> Expression {
    self.into()
  }

}
