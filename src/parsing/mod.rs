/*!

Parsing strings to expressions.

*/

mod lexer;
mod operator;
mod parser;

pub use parser::parse;


#[cfg(test)]
mod tests {
  #[test]
  fn it_works() {
    assert_eq!(2 + 2, 4);
  }
}
