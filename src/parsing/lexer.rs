/*!

Minimalist lexer.

*/

use std::{
  fmt::{Display, Formatter},
  cmp::min
};
use std::iter::Peekable;

use lazy_static::lazy_static;
use aho_corasick::{AhoCorasickBuilder, AhoCorasick, MatchKind};
use regex::{
  Regex,
  Match as RegexMatch
};
use rug::{
  Integer as BigInteger,
  Float as BigFloat,
  ops::{CompleteRound},
  Complete
};
use strum_macros::AsRefStr;

use crate::{
  atom::Atom,
  interner::{
    interned,
    resolve_str,
    InternedString
  }
};

/*
To have dynamic lexing of operators, the lexer needs facilities for adding and removing operators.
*/

/// We want the Lexer to be peekable.
pub type Lexer<'t> = Peekable<LexerCore<'t>>;

// Todo: This free function is a little awkward.
pub fn new_lexer(input: &str) -> Lexer {
  LexerCore::new(input).peekable()
}


// Keep in sync with numbering in `TOKENS`.
const STRING_LITERAL_IDX: usize = 0;
const REAL_IDX          : usize = 1;
const INTEGER_IDX       : usize = 2;
const IDENTIFIER_IDX    : usize = 3;
const EOL_COMMENT_IDX   : usize = 4;
const WHITESPACE_IDX    : usize = 5;

lazy_static! {
  pub static ref REGEXES: [Regex; 6] = [
    Regex::new(r#""(?:[^"]|\\")*""#).unwrap(),    //  0. StringLiteral  todo: Make strings more sophisticated.
    Regex::new(r"[0-9]+\.[0-9]+").unwrap(),       //  1. Real
    Regex::new(r"[0-9]+").unwrap(),               //  2. Integer
    Regex::new(r"[a-zA-Z][a-zA-Z0-9]*").unwrap(), //  3. Identifiers,
    Regex::new(r"//.*\n?").unwrap(),              //  4. EOL Comments
    Regex::new(r"[ \t\n\f]+").unwrap(),           //  5. Whitespace
  ];
}

static TOKENS: [&'static str; 26] = [
  r"___", //  6. BlankSequence
  r"==",  //  7. SameQ
  r"^=",  //  8. UpSet
  r":=",  //  9. SetDelayed
  r"^:=", // 10. UpSetDelayed
  r"=.",  // 11. Clear
  r"/;",  // 12. Condition
  r"[[",  // 13. OpenIndex
  r"]]",  // 14. CloseIndex
  r"__",  // 15. Sequence
  r"[",   // 16. Construct
  r"]",   // 17. CloseConstruct
  r"√",   // 18. Root
  r"^",   // 19. Power
  r"-",   // 20. Minus or Subtract
  r"*",   // 21. Times
  r"/",   // 22. Divide
  r"+",   // 23. Plus
  r"=",   // 24. Set
  r",",   // 25. Sequence
  r"(",   // 26. OpenParenthesis
  r")",   // 27. CloseParenthesis
  r"_",   // 28. Blank
  r";",   // 29. Statement separator
  r"{",   // 30. OpenCurlyBrace
  r"}",   // 31. CloseCurlyBrace
];


// The Lexer supplies `Token` variants to the client code.
#[derive(Clone, Debug, PartialEq, AsRefStr)]
pub enum Token {
  Integer(BigInteger),
  Operator(InternedString),
  Real(BigFloat),
  String(InternedString),
  Symbol(InternedString),
  Error(String),
}

impl Display for Token {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      Token::Integer(v) => {
        write!(f, "{}({})", self.as_ref(), v)
      }
      Token::Operator(v) => {
        write!(f, "{}({})", self.as_ref(), resolve_str(*v))
      }
      Token::Real(v) => {
        write!(f, "{}({})", self.as_ref(), v)
      }
      Token::String(v) => {
        write!(f, "{}(\"{}\")", self.as_ref(), resolve_str(*v))
      }
      Token::Symbol(v) => {
        write!(f, "{}({})", self.as_ref(), resolve_str(*v))
      }
      Token::Error(v) => {
        write!(f, "{}({})", self.as_ref(), v)
      }
    }
  }
}

impl Token {

  /// Leaf tokens can be trivially converted to `Atoms`.
  pub fn try_into_atom(self) -> Result<Atom, ()>{
    match self {
      Token::Operator(_)
      | Token::Error(_) => { Err(())}

      // Literals and symbols are the leaf tokens.
      Token::Integer(n) => Ok(Atom::Integer(n)),
      Token::Real(r)    => Ok(Atom::Real(r)),
      Token::String(s)  => Ok(Atom::String(s)),
      Token::Symbol(s)  => Ok(Atom::Symbol(s)),
    }
  }
}


pub struct LexerCore<'t>  {
  token_matcher: AhoCorasick,
  /// A cursor pointing to the start of the next token to be tokenized.
  start: usize,
  text: &'t str,
}

impl<'t> LexerCore<'t> {

  pub fn new(text: &'t str) -> Self {
    let token_matcher = AhoCorasickBuilder::new()
        .anchored(true)
        .auto_configure(&TOKENS)
        .match_kind(MatchKind::LeftmostLongest)
        .build(TOKENS);

    LexerCore {
      token_matcher,
      start: 0,
      text
    }
  }

  // This method is a copy+paste, because `aho_corasick::Match` is a different type from `regex::Match`.
  // todo: Factor out this common code the right way.
  pub(crate) fn get_operator_match(&mut self) -> Result<InternedString, Token> {
    match self.token_matcher.find(&self.text[self.start..]) {
      Some(token) => {

        if token.start() != 0{
          // Token must start at beginning of the string.
          let error_start: usize = self.start;
          self.start += token.start(); // Skip over this unrecognized token.
          // Don't print text of unbounded length.
          let error_end: usize = min(error_start + 20, error_start + token.end());
          Err(Token::Error(format!("Unexpected token: {}", &self.text[error_start..error_end])))

        } else {
          let start = self.start;
          let end = self.start + token.end();
          self.start = end;
          Ok(interned(
            &self.text[start..end]
          ))
        }
      }
      None => Err(Token::Error("No matching tokens found.".to_string()))
    }
  }

  /// Processes matches resulting from `regex.find(&self.text[self.start..])`, updating `self.start` appropriately.
  fn get_match(&mut self, found: Option<RegexMatch>) -> Result<InternedString, Token> {

    match found {

      Some(token) => {
        if token.start() != 0{
          // Token must start at beginning of the string.
          let error_start: usize = self.start;
          self.start += token.start(); // Skip over this unrecognized token.
          // Don't print text of unbounded length.
          let error_end: usize = min(error_start + 20, error_start + token.end());
          Err(Token::Error(format!("Unexpected token: {}", &self.text[error_start..error_end])))

        } else {
          let start = self.start;
          let end = self.start + token.end();
          self.start = end;
          Ok(interned(
            &self.text[start..end]
          ))
        }
      } // end found match

      None=>{
        // Error!
        Err(Token::Error("No matching tokens found.".to_string()))
      } // end found no match

    } // end match on found token match

  }

}

impl<'t> Iterator for LexerCore<'t> {
  type Item = Token;

  // todo: Decide if we want to automatically convert leaves to Atoms, in which case we only need three `Token`
  //       variants: Error(String), Operator(InternedString), Leaf(Atom). Leaving as a token allows parsing based on
  //       leaf type, which is required for the hypothetical future.
  fn next(&mut self) -> Option<Self::Item> {
    // Eat whitespace.
    let stripped = self.text[self.start..].trim_start();
    self.start = self.text.len() - stripped.len();

    // todo: Eat EOL comments.

    // Empty state
    if self.start == self.text.len() {
      return None;
    }

    match self.text[self.start..].as_bytes()[0] {
      b'"' => {
        // Lex string literal.
        match
          self.get_match(REGEXES[STRING_LITERAL_IDX].find(&self.text[self.start..])){
          Ok(interned_string) => {
            Some(Token::String(interned_string))
          }
          Err(t) => Some(t)
        }

      }

      c if char::is_ascii_digit(&(c as char)) => {
        // Lex number literal. Note that reals must begin with a digit, not `.`.
        match
          self.get_match(REGEXES[REAL_IDX].find(&self.text[self.start..])) {
          Ok(token) => {
            Some(Token::Real(BigFloat::parse(resolve_str(token)).unwrap().complete(53)))
          },
          Err(_) => {
            Some(
              Token::Integer(
                BigInteger::parse(
                  resolve_str(
                    self.get_match(REGEXES[INTEGER_IDX].find(&self.text[self.start..])).unwrap()
                  )
                ).unwrap().complete()
              )
            )
          }
        }
      }

      c if char::is_alphabetic(c as char) => {
        // Lex identifier.
        match
          self.get_match(REGEXES[IDENTIFIER_IDX].find(&self.text[self.start..]))
        {
          Ok(interned_string) => {
            Some(Token::Symbol(interned_string))
          }
          Err(t) => Some(t)
        }
      }

      _ => {
        // Lex operator
        match self.get_operator_match() {
          Ok(interned_string) => Some(Token::Operator(interned_string)),
          Err(t) => Some(t)
        }
      } // end if non-regex token

    } // end match on first character
  }

}


// See `Parser` for tests.

// #[cfg(test)]
// mod tests {
//   #[test]
//   fn it_works() {
//     assert_eq!(2 + 2, 4);
//   }
// }
