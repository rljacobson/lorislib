/*!

Minimalist lexer.

*/

use std::{
  fmt::{Display, Formatter},
  cmp::min,
};

use lazy_static::lazy_static;
use aho_corasick::{
  AhoCorasickBuilder,
  AhoCorasick,
  MatchKind,
  StartKind,
  Input,
  Anchored
};
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
  built_ins::DEFAULT_REAL_PRECISION,
  atom::Atom,
  interner::{
    interned,
    resolve_str,
    InternedString
  },
  logging::{Channel, log}
};

/*
To have dynamic lexing of operators, the lexer needs facilities for adding and removing operators.
*/

// We want the Lexer to be peekable. However, using `Peekable<I>` is incompatible with `expect()`, which changes
// matching strategies and invalidates the peeked token. Since lexing is so cheap, we just lex without updating state
// for `peek()`.
// pub type Lexer<'t> = Peekable<LexerCore<'t>>;


// Keep in sync with numbering in `TOKENS`.
const STRING_LITERAL_IDX: usize = 0;
const REAL_IDX          : usize = 1;
const INTEGER_IDX       : usize = 2;
const IDENTIFIER_IDX    : usize = 3;
const WHITESPACE_IDX    : usize = 4;
// const COMMENT_IDX       : usize = 5;

lazy_static! {
  pub static ref REGEXES: [Regex; 4] = [
    // Any non -quote or -slash; any even number of slashes; an escaped character (including quote); and repeat as many
    // times as possible.
    Regex::new(r#""(?:[^"\\]|\\\\|\\.)*""#).unwrap(), //  0. StringLiteral  todo: Make strings more sophisticated.
    Regex::new(r"[0-9]+\.[0-9]+").unwrap(),           //  1. Real
    Regex::new(r"[0-9]+").unwrap(),                   //  2. Integer
    Regex::new(r"[a-zA-Z][a-zA-Z0-9]*").unwrap(),     //  3. Identifiers,
    // Regex::new(r"[ \t\n\f]+").unwrap(),            //  4. Whitespace
  ];
}

static TOKENS: [&'static str; 32] = [
  "___", //  IntoBlankNullSequence
  "__",  //  IntoBlankSequence
  "_",   //  IntoBlank
  "[[",  //  Part
  "]]",  //  Part
  "[",   //  Construct
  "]",   //  Construct
  "^",   //  Power
  "-",   //  Minus
  "*",   //  Times
  "/",   //  Divide
  "-",   //  Subtract
  "+",   //  Plus
  "&&",  //  And
  "||",  //  Or
  "===", //  SameQ
  "==",  //  Equal
  "/;",  //  Condition
  ":>",  //  RuleDelayed
  "->",  //  Rule
  "/.",  //  ReplaceAll
  "=",   //  Set
  "^=",  //  UpSet
  ":=",  //  SetDelayed
  "^:=", //  UpSetDelayed
  "=.",  //  Unset
  ",",   //  Sequence
  ";",   //  CompoundExpression
  "(",   //  Sequence
  ")",   //  Sequence
  "{",   //  List
  "}",   //  List
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


pub struct Lexer<'t>  {
  token_matcher: AhoCorasick,
  /// A cursor pointing to the start of the next token to be tokenized.
  start: usize,
  text: &'t str,
}

impl<'t> Lexer<'t> {

  pub fn new(text: &'t str) -> Self {
    let token_matcher = AhoCorasickBuilder::new()
        .start_kind(StartKind::Anchored)
        // .auto_configure(&TOKENS)
        .match_kind(MatchKind::LeftmostLongest)
        .build(TOKENS)
        .unwrap();

    Lexer {
      token_matcher,
      start: 0,
      text
    }
  }

  /// Skips over whitespace and comments.
  fn eat_ignorables(&mut self) -> Result<(), ()> {
    loop {
      let old_start = self.start;

      // Eat whitespace.
      let mut character = self.text[self.start..].char_indices();
      let mut skipped = 0; // A count of whitespace characters skipped (sort of, counts bytes).
      while let Some((position, c)) = character.next() {
        if !c.is_whitespace() {
          break;
        }
        skipped = position + 1;
      }
      self.start += skipped;

      // Eat comments. We don't care about the result of the match, only that `get_match` updated `self.start`.
      self.eat_comments()?;

      // If neither of these moved the start, we're done.
      if old_start == self.start {
        return Ok(());
      }
    }
  }

  /// Scans comments.
  fn eat_comments(&mut self) -> Result<(), ()> {
    if self.text[self.start..].starts_with("(*") {
      log(
        Channel::Debug,
        6,
        "Comment opened."
      );

      let mut character = self.text[self.start+2..].char_indices().peekable();
      loop{
        if let Some((p, c)) = character.next(){


          match (p, c) {
            (_, '\\') => {
              log(
                Channel::Debug,
                6,
                "Found escaped."
              );
              // An escaped character. Skip over it.
              character.next();
            }

            (_, '*') => {
              log(
                Channel::Debug,
                6,
                "Found *, peeking."
              );
              if let Some(&(p, ')')) = character.peek(){
                // Close of comment.
                // character.next();
                // self.start += p;
                log(
                  Channel::Debug,
                  4,
                  format!(
                    "COMMENT:\n\"{}\"",
                    &self.text[self.start..self.start+p+3]
                  ).as_str()
                );
                self.start += p + 3;
                return Ok(());
              } else if let Some(&(_, c)) = character.peek(){
                log(
                  Channel::Debug,
                  6, format!("Not closing, found `{}`.", c).as_str()
                );
              }
            }

            _ => continue
          }
        } else {
          break;
        } // end destructure next character.
      } // end loop

      // if we get this far then the comment is unterminated.
      log(
        Channel::Error,
        1,
        format!(
          "Unterminated comment starting at byte offset {}.",
          self.start
        ).as_str()
      );
      return Err(());
    }
    // No open comment
    Ok(())
  }

  // This method is a copy+paste, because `aho_corasick::Match` is a different type from `regex::Match`.
  // todo: Factor out this common code the right way: Make supertrait, implement it for both types.
  fn get_operator_match(&mut self) -> Result<InternedString, Token> {
    // Warning: Automatic coercion of `&str` to `Input` is always unanchored.
    // See https://github.com/BurntSushi/aho-corasick/issues/114 for details.
    let haystack = Input::new(&self.text[self.start..]).anchored(Anchored::Yes);
    match self.token_matcher.find(haystack) {
      Some(token) => {

        if token.start() != 0{
          eprintln!("OPERATOR MATCHER FAILED");
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

  /// Looks for the given token before falling back to the normal leftmost longest strategy. Assumes `expected` is an
  /// OpToken. Consumes the token.
  pub fn expect(&mut self, expected: InternedString) -> Option<Token> {

    if self.eat_ignorables().is_err() {
      // Unterminated comment.
      return None;
    }

    let expected_str = resolve_str(expected);

    if self.text[self.start..].starts_with(expected_str){
      self.start += expected_str.len();
      Some(
        Token::Operator(expected)
      )
    } else {
      self.next()
    }
  }

  /// Returns the next token without consuming it, i.e. without updating *any* state of the lexer.
  /// Requires `&mut self` because it's much easier to restore previous state than to not change state in the first
  /// place.
  pub fn peek(&mut self) -> Option<Token> {
    let old_start = self.start;
    let result = self.next();
    self.start = old_start;

    result
  }

}

impl<'t> Iterator for Lexer<'t> {
  type Item = Token;

  // todo: Decide if we want to automatically convert leaves to Atoms, in which case we only need three `Token`
  //       variants: Error(String), Operator(InternedString), Leaf(Atom). Leaving as a token allows parsing based on
  //       leaf type, which is required for the hypothetical future.
  fn next(&mut self) -> Option<Self::Item> {

    if self.eat_ignorables().is_err() {
      // Unterminated comment.
      return None;
    }

    // No text remaining.
    if self.start == self.text.len() {
      return None;
    }
    let old_start  = self.start;


    match self.text[self.start..].as_bytes()[0] {
      b'"' => {
        // Lex string literal.
        match self.get_match(REGEXES[STRING_LITERAL_IDX].find(&self.text[self.start..]))
        {
          Ok(interned_string) => {
            Some(Token::String(interned_string))
          }

          // Unterminated string
          Err(_) => Some(Token::Error(format!( "Unterminated string starting at byte {}", old_start)))
        }

      }

      c if char::is_ascii_digit(&(c as char)) => {
        // Lex number literal. Note that reals must begin with a digit, not `.`.
        match
          self.get_match(REGEXES[REAL_IDX].find(&self.text[self.start..])) {
          Ok(token) => {
            Some(Token::Real(BigFloat::parse(resolve_str(token)).unwrap().complete(DEFAULT_REAL_PRECISION)))
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
