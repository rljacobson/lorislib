/*!

Quick and dirty parser for an M-expression language.

 */
// #![cfg(feature = "alloc")]


use std::rc::Rc;

use nom::{
  branch::alt,
  bytes::{
    complete::{
      tag,
      take_until,
      is_not,
      is_a,
      take_while_m_n
    }
  },
  character::{
    complete::{
      alphanumeric0,
      alpha1,
      char as char1,
      multispace1,
      one_of
    }
  },
  combinator::{
    map,
    map_res,
    recognize,
    map_opt,
    value,
    verify
  },
  error::{
    ErrorKind,
    FromExternalError,
    ParseError
  },
  IResult,
  multi::{
    many0,
    fold_many0,
    many1,
    separated_list1
  },
  number::complete::{
    recognize_float_parts,
  },
  sequence::{
    delimited,
    pair,
    preceded,
    separated_pair,
    terminated
  },
};

use crate::{
  atoms::{Function, Literal, Symbol, Variable, Sequence, SequenceVariable},
  attributes::{Attribute, Attributes},
  expression::{Expression, RcExpression},
  matching::MatchEquation
};

pub fn parse_program(input: &str) -> IResult<&str, MatchEquation> { //Vec<RcExpression>

  // many0(
  //   delimited(
  //     many0(ignorable),
  //     statement,
  //     many0(ignorable)
  //   )
  // )(input)

  delimited(
    many0(ignorable),
    match_expression,
    many0(ignorable)
  )(input)

}

fn ignorable(input: &str) -> IResult<&str, &str> {
  recognize(
    many0(
      alt((
        is_a(" \t\n\r"),
        comment
      ))
    )
  )(input)
}


/// A combinator that takes a parser `inner` and produces a parser that also consumes both leading and
/// trailing whitespace, returning the output of `inner`.
fn ignore_ignorables<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O, nom::error::Error<&str>>
  where
      F: Fn(&'a str) -> IResult<&'a str, O, nom::error::Error<&str> >,
{
  delimited(
    ignorable,
    inner,
    ignorable
  )
}


// Atomic expressions

fn comment(input: &str) -> IResult<&str, &str> {
  alt((
    preceded(
      tag("//"),
      is_not("\n\r")
    ),
    delimited(tag("/*"), take_until("*/"), tag("*/"))
  ))
  (input)
}


fn identifier(input: &str) -> IResult<&str, &str> {
  recognize(
    pair(
      alt((alpha1, tag("ƒ"))),
      alphanumeric0
    )
  )(input)
}


fn literal(input: &str) -> IResult<&str, RcExpression> {
  let val = alt((
    recognize(parse_string),
    recognize(recognize_float_parts),
    recognize(hexadecimal),
    recognize(decimal),
    // etc.
  ))(input)?;

  let expr = Rc::new(Literal(val.1.to_string()).into());

  Ok((val.0, expr))
}


fn hexadecimal(input: &str) -> IResult<&str, &str> { // <'a, E: ParseError<&'a str>>
  preceded(
    alt((tag("0x"), tag("0X"))),
    recognize(
      many1(
        terminated(one_of("0123456789abcdefABCDEF"), many0(char1('_')))
      )
    )
  )(input)
}


fn decimal(input: &str) -> IResult<&str, &str> {
  recognize(
    many1(
      terminated(one_of("0123456789"), many0(char1('_')))
    )
  )(input)
}


// Higher-order expressions

/// A function call is a name (symbol) or variable adjacent to a sequence. A sequence, function,
/// or literal cannot be the "head" of a function.
fn function_application(input: &str) -> IResult<&str, RcExpression> {
  let val = pair(
    alt((symbol, variable)),
    sequence
  )(input)?;

  let mut attributes = Attributes::new();
  attributes.set(Attribute::Associative);
  attributes.set(Attribute::Commutative);
  attributes.set(Attribute::Variadic);



  if let Expression::Sequence(sequence) = Rc::<Expression>::try_unwrap(val.1.1).unwrap() {
    let f = Function{
      head: val.1.0.clone(),
      children: sequence.children,
      attributes
    };

    Ok((val.0, Rc::new(f.into())))
  } else {
    unreachable!()
  }


}


fn variable(input: &str) -> IResult<&str, RcExpression> {
  let val = delimited(
    char1('‹'),
    identifier,
    char1('›')
  )(input)?;

  let expr: RcExpression = Rc::new(Variable(val.1.to_string()).into());

  Ok((val.0, expr))
}

fn symbol(input: &str) -> IResult<&str, RcExpression> {
  let val = identifier(input)?;
  let expr: RcExpression = Rc::new(Symbol(val.1.to_string()).into());

  Ok((val.0, expr))
}


fn sequence_variable(input: &str) -> IResult<&str, RcExpression> {
  let val = delimited(
    char1('«'),
    identifier,
    char1('»')
  )(input)?;

  let expr: RcExpression = Rc::new(SequenceVariable(val.1.to_string()).into());

  Ok((val.0, expr))
}


fn expression(input: &str) -> IResult<&str, RcExpression> {
  delimited(
    ignorable,
    alt((
      function_application,
      sequence,
      symbol,
      literal,
      variable,
      sequence_variable,
    )),
    ignorable
  )(input)
}


fn sequence(input: &str) -> IResult<&str, RcExpression> {
  let val = delimited(
    alt((char1('('), char1('❨'))),
    separated_list1(
      char1(','),
      expression
    ),
    alt((char1(')'), char1('❩')))
  )(input)?;

  let seq = Sequence{
    children: val.1
  };
  let expr: RcExpression = Rc::new(seq.into());

  Ok((val.0, expr))
}


fn match_operator(input: &str) -> IResult<&str, &str> {
  alt((
    tag("<<"),
    tag("≪")
  ))(input)
}


fn match_expression(input: &str) -> IResult<&str, MatchEquation> {
  let val = separated_pair(
    expression,
    match_operator,
    expression
  )(input)?;

  let me = MatchEquation{
    pattern: val.1.0,
    ground: val.1.1
  };

  Ok((val.0, me))
}



// region String Parsing

/*
The following is taken verbatim from the Nom example of how to parse an escaped string. The rules
for the string are similar to JSON and rust. A string is:

- Enclosed by double quotes
- Can contain any raw unescaped code point besides \ and "
- Matches the following escape sequences: \b, \f, \n, \r, \t, \", \\, \/
- Matches code points like Rust: \u{XXXX}, where XXXX can be up to 6
  hex characters
- an escape followed by whitespace consumes all whitespace between the
  escape and the next non-whitespace character
*/

/// Parse a unicode sequence, of the form u{XXXX}, where XXXX is 1 to 6
/// hexadecimal numerals. We will combine this later with parse_escaped_char
/// to parse sequences like \u{00AC}.
fn parse_unicode<'a, E>(input: &'a str) -> IResult<&'a str, char, E>
  where
      E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>,
{
  // `take_while_m_n` parses between `m` and `n` bytes (inclusive) that match
  // a predicate. `parse_hex` here parses between 1 and 6 hexadecimal numerals.
  let parse_hex = take_while_m_n(1, 6, |c: char| c.is_ascii_hexdigit());

  // `preceded` takes a prefix parser, and if it succeeds, returns the result
  // of the body parser. In this case, it parses u{XXXX}.
  let parse_delimited_hex = preceded(
    char1('u'),
    // `delimited` is like `preceded`, but it parses both a prefix and a suffix.
    // It returns the result of the middle parser. In this case, it parses
    // {XXXX}, where XXXX is 1 to 6 hex numerals, and returns XXXX
    delimited(char1('{'), parse_hex, char1('}')),
  );

  // `map_res` takes the result of a parser and applies a function that returns
  // a Result. In this case we take the hex bytes from parse_hex and attempt to
  // convert them to a u32.
  let parse_u32 = map_res(parse_delimited_hex, move |hex| u32::from_str_radix(hex, 16));

  // map_opt is like map_res, but it takes an Option instead of a Result. If
  // the function returns None, map_opt returns an error. In this case, because
  // not all u32 values are valid unicode code points, we have to fallibly
  // convert to char with from_u32.
  map_opt(parse_u32, |value| std::char::from_u32(value))(input)
}

/// Parse an escaped character: \n, \t, \r, \u{00AC}, etc.
fn parse_escaped_char<'a, E>(input: &'a str) -> IResult<&'a str, char, E>
  where
      E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>,
{
  preceded(
    char1('\\'),
    // `alt` tries each parser in sequence, returning the result of
    // the first successful match
    alt((
      parse_unicode,
      // The `value` parser returns a fixed value (the first argument) if its
      // parser (the second argument) succeeds. In these cases, it looks for
      // the marker characters (n, r, t, etc) and returns the matching
      // character (\n, \r, \t, etc).
      value('\n', char1('n')),
      value('\r', char1('r')),
      value('\t', char1('t')),
      value('\u{08}', char1('b')),
      value('\u{0C}', char1('f')),
      value('\\', char1('\\')),
      value('/', char1('/')),
      value('"', char1('"')),
    )),
  )(input)
}

/// Parse a backslash, followed by any amount of whitespace. This is used later
/// to discard any escaped whitespace.
fn parse_escaped_whitespace<'a, E: ParseError<&'a str>>(
  input: &'a str,
) -> IResult<&'a str, &'a str, E> {
  preceded(char1('\\'), multispace1)(input)
}

/// Parse a non-empty block of text that doesn't include \ or "
fn parse_literal<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
  // `is_not` parses a string of 0 or more characters that aren't one of the
  // given characters.
  let not_quote_slash = is_not("\"\\");

  // `verify` runs a parser, then runs a verification function on the output of
  // the parser. The verification function accepts out output only if it
  // returns true. In this case, we want to ensure that the output of is_not
  // is non-empty.
  verify(not_quote_slash, |s: &str| !s.is_empty())(input)
}

/// A string fragment contains a fragment of a string being parsed: either
/// a non-empty Literal (a series of non-escaped characters), a single
/// parsed escaped character, or a block of escaped whitespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StringFragment<'a> {
  Literal(&'a str),
  EscapedChar(char),
  EscapedWS,
}

/// Combine parse_literal, parse_escaped_whitespace, and parse_escaped_char
/// into a StringFragment.
fn parse_fragment<'a, E>(input: &'a str) -> IResult<&'a str, StringFragment<'a>, E>
  where
      E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>,
{
  alt((
    // The `map` combinator runs a parser, then applies a function to the output
    // of that parser.
    map(parse_literal, StringFragment::Literal),
    map(parse_escaped_char, StringFragment::EscapedChar),
    value(StringFragment::EscapedWS, parse_escaped_whitespace),
  ))(input)
}

/// Parse a string. Use a loop of parse_fragment and push all of the fragments
/// into an output string.
fn parse_string<'a, E>(input: &'a str) -> IResult<&'a str, String, E>
  where
      E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>,
{
  // fold_many0 is the equivalent of iterator::fold. It runs a parser in a loop,
  // and for each output value, calls a folding function on each output value.
  let build_string = fold_many0(
    // Our parser function– parses a single string fragment
    parse_fragment,
    // Our init value, an empty string
    String::new,
    // Our folding function. For each fragment, append the fragment to the
    // string.
    |mut string, fragment| {
      match fragment {
        StringFragment::Literal(s) => string.push_str(s),
        StringFragment::EscapedChar(c) => string.push(c),
        StringFragment::EscapedWS => {}
      }
      string
    },
  );

  // Finally, parse the string. Note that, if `build_string` could accept a raw
  // " character, the closing delimiter " would never match. When using
  // `delimited` with a looping parser (like fold_many0), be sure that the
  // loop won't accidentally match your closing delimiter!
  delimited(char1('"'), build_string, char1('"'))(input)
}

// endregion





#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn test_items() {
    let hex = "0xff4d";
    hexadecimal(hex).unwrap();

    let dec = "23409857";
    decimal(dec).unwrap();

    let text = "\"Hello, world!\"";
    parse_string::<(&str, ErrorKind)>(text).unwrap();

    let symb = "x";
    symbol(symb).unwrap();

    let seq = "(x, y, z)";
    sequence(seq).unwrap();

    let func = "ƒ(x, y, z)";
    function_application(func).unwrap();

    let v = "‹v›";
    variable(v).unwrap();

    let sv = "«s»";
    sequence_variable(sv).unwrap();

    let match_expr = "ƒ(‹u›, ‹v›) << ƒ(a, b)";
    match_expression(match_expr).unwrap();

    assert_eq!(2+2, 4);
  }
}
