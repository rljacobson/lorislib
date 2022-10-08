/*!

Minimal lexer. An unusual feature of this lexer/parser combination is that `Expression`s are created very early,
already in the lexer, instead of later in the parser. We only do this for leaf nodes.

*/

use std::fmt::{Display, Formatter};

use strum::{AsRefStr};
use logos::{Logos, Lexer};
// use inlinable_string::{InlinableString as SmallString, StringExt};

use crate::atoms::{Integer, Real, SequenceVariable, Symbol, Variable};
use crate::expression::{Expression};

// ToDo: Get rid of these string copies.

#[derive(Clone, PartialEq, Debug, Logos, AsRefStr )]
#[logos(subpattern decimal = r"[0-9][_0-9]*")]
#[logos(subpattern hex = r"[0-9a-fA-F][_0-9a-fA-F]*")]
#[logos(subpattern octal = r"[0-7][_0-7]*")]
#[logos(subpattern binary = r"[0-1][_0-1]*")]
#[logos(subpattern exp = r"[eE][+-]?[0-9][_0-9]*")]
pub enum Token {
  #[regex(r"([a-zA-Z]+___)|(«[a-zA-Z]+»)", make_sequence_variable) ]
  SequenceVariable(Expression),

  #[regex(r"([a-zA-Z]+_)|(‹[a-zA-Z]+›)", make_variable)]
  Variable(Expression),

  #[regex(r"[a-zA-Z]+", make_symbol)]
  Symbol(Expression),

  // Non-fancy Strings.
  // ToDo: Do more sophisticated string parsing.
  #[regex(r#""(?:[^"]|\\")*""#, make_string_literal)]
  StringLiteral(Expression),

  // No scientific notation.
  #[regex(r"[0-9]+\.[0-9]+", make_real)]
  Real(Expression),

  // #[regex(r"[0-9]+")]
  #[regex("(?&decimal)", make_integer)]
  Integer(Expression),

  // Todo: This list of operators needs to be changeable dynamically, which probably means not using Logos.
  #[token("[", to_string)]
  #[token("]", to_string)]
  #[token("(", to_string)]
  #[token(")", to_string)]
  #[token("*", to_string)]
  #[token("/", to_string)]
  #[token("-", to_string)]
  #[token("+", to_string)]
  #[token("√", to_string)]
  #[token("^", to_string)]
  #[token("=", to_string)]
  #[token(":=", to_string)]
  #[token("=.", to_string)]
  #[token(",", to_string)]
  OpToken(String), // Resolved in the parser.

  #[error]
  #[regex(r"//.*\n?", logos::skip)]    // EOL Comments
  #[regex(r"[ \t\n\f]+", logos::skip)] // Whitespace
  Error
}

impl Token {
  pub fn unwrap_expression(self) -> Result<Expression, ()> {
    match self {
      Token::Error
      | Token::OpToken(_) => Err(()),

      Token::SequenceVariable(exp) => Ok(exp),
      Token::Variable(exp) => Ok(exp),
      Token::Symbol(exp) => Ok(exp),
      Token::StringLiteral(exp) => Ok(exp),
      Token::Real(exp) => Ok(exp),
      Token::Integer(exp) => Ok(exp),
    }
  }
}

impl Display for Token {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      Token::SequenceVariable(sv) => {write!(f, "{}", sv)}
      Token::Variable(v) => {write!(f, "{}", v)}
      Token::Symbol(s) => {write!(f, "{}", s)}
      Token::StringLiteral(s) => {write!(f, "{}", s)}
      Token::Real(r) => {write!(f, "{}", r)}
      Token::Integer(n) => {write!(f, "{}", n)}
      Token::OpToken(op) => {write!(f, "{}", op)}
      Token::Error => {write!(f, "ErrorToken")}
    }
  }
}

fn make_sequence_variable(lex: &Lexer<Token>) -> Expression {
  let name = strip_variables(lex);
  SequenceVariable(name.to_string()).into()
}


fn make_variable(lex: &Lexer<Token>) -> Expression {
  let name = strip_variables(lex);
  Variable(name).into()
}

fn make_symbol(lex: &Lexer<Token>) -> Expression {
  Symbol(lex.slice().to_string()).into()
}

fn strip_variables(lex: &Lexer<Token>) -> String {
  lex.slice().trim_matches(|c| c=='‹' || c=='›' || c=='«' || c=='»' || c=='_').to_string()
}

fn make_string_literal(lex: &Lexer<Token>) -> Expression {
  Symbol(
    String::from(lex.slice().trim_matches(|c| c=='"'))
  ).into()
}

fn make_real(lex: &Lexer<Token>) -> Expression {
  Real(lex.slice().parse().unwrap()).into()
}

fn make_integer(lex: &Lexer<Token>) -> Expression {
  Integer(lex.slice().parse().unwrap()).into()
}

fn to_string(lex: &Lexer<Token>) -> String {
  String::from( lex.slice() )
}


#[cfg(test)]
mod tests {
  use logos::{Lexer, Logos};
  use crate::parsing::Token;

  #[test]
  fn lex_test() {
    let text = "3 +7 * 9.3 ^ f [a, b, c_, d___, :=,√] \"monkey\" ";
    let lexer = Token::lexer(text);

    for token in lexer {
      println!("{}", token)
    }
  }
}
