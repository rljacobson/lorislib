/*!



 */
mod parser;
mod operator;
mod lexer;

// Re-export `Parser`.
pub use parser::Parser;
use lexer::Token;



#[cfg(test)]
mod tests {
  #[test]
  fn it_works() {
    assert_eq!(2 + 2, 4);
  }
}
