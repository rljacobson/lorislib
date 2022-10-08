/*!
A parser owns the `OperatorTable` and parses the expression grammar, building a syntax tree along
the way. Because the `OperatorTable` drives the control flow of the parsing algorithm, the
`OperatorTable` and `Parser` are tightly coupled, with `OperatorTable` being a data structure
only and `Parser` holding all methods.

This design is an evolution of that described by Theodore Norvell, which itself is very similar to
the standard object oriented design and Pratt's original description. In the original design,
information about operators are stored in a table during runtime, and there are facilities for
loading, managing, and searching this table.

Norvell describes three tables: `LeftCommand`, `NullCommand`, and "Other." The "Command" suffix is
historical and refers to what command the parsing algorithm should take when it encounters a
particular token. `LeftCommand` holds data about operators that take a operand on their left.
Operators in `NullCommand` *start* expressions.

L (left) tokens:  Takes a left operand (binary ops, postfix ops).
                  L tokens are those directly consumed by the E procedure.
N (null) tokens:  No left operand (prefix ops and variables).
                  N tokens are those that are used to make the initial
                  choice in the P procedure and that are then consumed as
                  opposed to leading to an error being reported
O (other) tokens: All other tokens: ), ], etc.

See Theodore S. Norvell, "From Precedence Climbing to Pratt Parsing," 2016:
https://www.engr.mun.ca/~theo/Misc/pratt_parsing.htm

The present design differs in several ways:
  1. Operator data is stored in a single table.
  2. An operator may have any (or all) of L-, N-, and O-tokens. If an operator has no token of a
     category, the column for that category is set to NULL.
  3. Methods for parsing operators are moved out of operator (sub)classes and into the `Parser`
     with the rest of the parsing code. This not only consolidates the parsing code but also
     separates the concerns of describing data about an operator from the parsing algorithm.

There are other incidental differences:
  * For simplicity, we use a design in which we conflate tokens with nodes of the
    abstract syntax tree. In practice, a more sophisticated language might have a `Token` struct as
    a layer beneath (prior to) `ASTNode`.
  * The lexer is trivial.

*/
#![allow(dead_code)]

use core::iter::Peekable as TokenIterator;
use std::{
  rc::Rc
};

use logos::{Logos, Lexer};

use crate::{
  atoms::{
    Function,
  },
  expression::{
    Expression,
    RcExpression,
  },
  logging::{
    log,
    Channel,
  },
  parsing::{
    lexer::Token,
    operator::{
      Operator
    }
  }
};
use crate::parsing::operator::{get_operator_table, OperatorTable};

const INF: i32 = i32::MAX;

pub struct Parser<'t> {
  pub root_node : Option<RcExpression>,
  operator_table: OperatorTable,
  lexer         : TokenIterator<Lexer<'t, Token>>,
  error_occurred: bool,
}

impl<'t> Parser<'t> {

  pub fn new(text: &str) -> Parser {
    // Load operator database from file.
    let op_table = get_operator_table();
    // println!("OpTable: {:?}", &op_table);

    Parser{
      operator_table: op_table,
      root_node     : None,
      lexer         : Token::lexer(text).peekable(),
      error_occurred: false,
    }
  }


  pub fn parse(&mut self) -> Result<RcExpression, ()>{
    // Bootstrap the parsing algorithm...
    match self.parse_expression(0) {

      Ok(exp) => {
        if self.error_occurred {
          log(Channel::Error, 1, "Succeeded parsing with errors.");
        }
        Ok(Rc::new(exp))
      },

      Err(token) => {
        log(Channel::Error, 1, format!("Unexpected: {:?}", &token).as_str());
        Err(())
      }

    }
  }

  #[allow(non_snake_case)]
  fn parse_expression(&mut self, previous_binding_power: i32) -> Result<Expression, Token> {

    // STEP 1: Parse null tokens, i.e. tokens that can begin an expression. Includes leaf tokens.

    let mut token = self.consume_token();
    log(Channel::Debug, 5, format!("Consuming token: {}", &token).as_str());

    // Convert the token to an expression. The `current_root` holds the root of the expression we are currently
    // parsing. Get the operator record for the token to drive the parsing algorithm. If the expression is a leaf, a
    // generic `NULLARY_OPERAND` operator record is returned. The `NULLARY_OPERAND` is distinguished by having an
    // arity of 0, as a leaf must.
    let (mut current_root, operator): (Expression, Operator) = self.lookup_expression_operator(&token)?;
    log(Channel::Debug, 5, format!("Parsed expression: {}", &current_root).as_str());


    // Parses the stuff that follows this token if this token is a null token (i.e. can begin an expression). If the
    // token is a leaf, this is a no-op. Modifies `current_root` in place.
    self.null_denotation(&mut current_root, &operator)
        .map_err(|_| token.clone())?;

    // STEP 2: Parse left tokens, i.e. tokens that take an expression on their left. Includes all infix operators.

    // let mut r: i32 = INF;
    loop {
      // Don't consume in case binding power is out of bound.
      token = match self.get_current_token() {
        Some(tok) => tok.clone(),
        None => { return Ok(current_root); }
      };
      log(Channel::Debug, 5, format!("Peeking, found token: {}", &token).as_str());
      // Look up the operator information for the expression we are currently parsing
      // based on the value of token. The operator knows it's left and
      // next binding power.

      let (mut new_root, operator): (Expression, Operator) = self.lookup_expression_operator(&token)?;

      if previous_binding_power > operator.left_binding_power() {
        log(
          Channel::Debug,
          5,
          format!(
            "Found expression but binding power out of range: p={}, exp.lbp={}",
            &previous_binding_power,
            operator.left_binding_power()
          ).as_str()
        );
        break;
      }

      self.consume_token();
      log(Channel::Debug, 5, format!("Found expression: {}. Consuming peeked token.", &new_root).as_str());

      // Parse the RHS of the expression.
      self.left_denotation(current_root, &mut new_root, &operator)
          .map_err(|_| token)? ;
      // r = operator.next_binding_power();

      current_root = new_root;
    }

    return Ok(current_root);

  }

  fn lookup_expression_operator(&self, token: &Token) -> Result<(Expression, Operator), Token> {
    match &token {

      Token::OpToken(_) => {
        match self.operator_table.look_up(token) {

          Some(op) => {
            // Operators become function calls: `a+b` -> `Add[a, b]`.
            let expression = Function::with_symbolic_head(op.name.as_str()).into();
            Ok((expression, op.clone()))
          }

          None => {
            // An `OpToken` should never contain a leaf token, only things that are in the operator table.
            log(Channel::Error, 1, format!("Unexpected: {:?}", &token).as_str());
            return Err(token.clone());
          }

        }
      } // end match OpToken

      Token::Error => {
        // An `OpToken` should never contain a leaf token, only things that are in the operator table.
        log(Channel::Error, 1, format!("Unexpected: {:?}", &token).as_str());
        return Err(token.clone());
      }

      any_other_token => {
        // This is the leaf node case.
        let exp = (*any_other_token).clone().unwrap_expression().unwrap();
        let op = Operator::nullary_operand();
        Ok((exp, op))
      }

    } // end match token
  }

  /// Fetches the next token and consumes it. This is the default `next` behavior. The alternative behavior is
  /// `peek`, which does not consume the token from the iterator.
  fn consume_token(&mut self) -> Token {
    // This *should* be infallible, because errors should produce error tokens.
    self.lexer.next().unwrap()
  }

  /// Fetches the next token but does not consume it. A call to either `get_current_token` or `consume_next_token`
  /// will return the same token again.
  fn get_current_token(&mut self) -> Option<&Token> {
    self.lexer.peek()
  }

  /// This method parses all expressions that have null tokens, that is, all expressions with tokens that can begin
  /// an expression.
  fn null_denotation(&mut self, expression: &mut Expression, operator: &Operator) -> Result<(), ()> {
    // For tokens that don't begin an expression, do nothing.
    if operator.arity == 0 || operator.n_token.is_none() {
      return Ok(());
    }

    // todo: What do we do for, e.g. matchfix that is optionally empty?
    if let Some(expected_token) = &operator.o_token {
      match self.parse_expression(0) {
        // The nonempty case
        Ok(child_expression) => {
          push_child(expression, child_expression)?
        }

        // The empty case.
        Err(_token) => {
          // log(
          //   Channel::Error,
          //   1,
          //   format!("Expected: {}, Found: {:?}", expected_token, &token).as_str()
          // );
          // self.error_occurred = true;
          // return Err(());
        }
      }


      self.expect(expected_token)?;
    }

    // nt exp1 ot exp2
    if operator.arity == 2 {
      match self.parse_expression(0) {
        // The nonempty case
        Ok(child_expression) => {
          push_child(expression, child_expression)?;
        }

        // The empty case.
        Err(token) => {
          log(
            Channel::Error,
            1,
            format!("Another expression expected. Found: {:?}", &token).as_str()
          );
          self.error_occurred = true;
          return Err(());
        }
      }
    }

    Ok(())
  }


  fn expect(&mut self, token_text: &String) -> Result<(), ()> {
    match self.consume_token() {

      Token::OpToken(t) if t==*token_text => {
        Ok(())
      }

      anything_else => {
        log(Channel::Error, 1, format!("Expected: {}, Found: {}", token_text, anything_else).as_str());
        self.error_occurred = true;
        Err(())
      }

    }
  }

  // Given the LHS expression and an operator, parse the RHS expression.
  fn left_denotation(&mut self, lhs: Expression, root: &mut Expression, operator: &Operator)
    -> Result<(), ()>{
    log(
      Channel::Debug,
      1,
      format!(
        "Now tying to parse RHS (in LeD). lhs={} root={} op.rbp={}",
        &lhs,
        root,
        operator.right_binding_power()
      ).as_str()
    );
    let rhs =
        match self.parse_expression(operator.right_binding_power()) {
          Ok(exp) => exp,
          Err(token) => {
            log(
              Channel::Error,
              1,
              format!("[LeD] Another expression expected. Found: {:?}", &token).as_str()
            );
            self.error_occurred = true;
            return Err(());
          }
        };
    push_child(root, lhs)?;
    push_child(root, rhs)?;
    log(
      Channel::Debug,
      1,
      format!("RHS successfully parsed. Inserted LHS, RHS as children: {}", &root).as_str()
    );

    // A left token can also have an other token, as with `[` in `f[x]`.
    if let Some(o_token) = &operator.o_token {
      log(
        Channel::Debug,
        1,
        format!("Now \"expect\"ing O_TOKEN: {}", &o_token).as_str()
      );
      self.expect(o_token)?;
    }

    Ok(())
  }

}

///
fn push_child(parent: &mut Expression, child: Expression) -> Result<(), ()> {
  // Fix up function construct.
  let parent_is_construct  = (parent.name()=="Construct");
  // Fix up in-line sequences.
  let child_is_sequence    = (child.name()=="Sequence");
  let child_is_parentheses = (child.name()=="Parentheses");

  // Destructure parent…
  return match parent {
    Expression::Function(expr) => {
      if parent_is_construct && expr.children.is_empty() {
        // The first argument to `Construct` is the head.
        expr.head = Rc::new(child);
        // Subsequent calls to `push_child()` will not execute this branch.
        return Ok(());
      }
      if child_is_sequence || child_is_parentheses{
        // Destructure child…
        if let Expression::Function(mut child_expr) = child {
          // Splice in the sequence's children.
          expr.children.append(&mut child_expr.children);
          return Ok(());
        }
      }

      // If we get here it's just a normal child of a normal function.
      expr.push(Rc::new(child));
      Ok(())
    }

    Expression::Sequence(expr) => {
      if child_is_sequence || child_is_parentheses {
        // Destructure child…
        if let Expression::Function(mut child_expr) = child {
          // Splice in the sequence's children.
          expr.children.append(&mut child_expr.children);
          return Ok(());
        }
        // Is the child ever a true `Expression::Sequence` ? If so, change the if-let to a match.
      }
      // If we get here it's just a normal child of a normal function.
      expr.push(Rc::new(child));
      Ok(())
    }

    _ => {
      Err(())
    }
  }

}



#[cfg(test)]
mod tests {
  use crate::logging::set_verbosity;
  use super::*;

  #[test]
  fn function_test() {
    let text = "3.8*f[1+x, y]";
    // let text = "f[1+3.8]";
    // set_verbosity(5);
    let mut parser = Parser::new(text);

    match parser.parse() {

      Ok(e) => {
        assert_eq!("Times[3.8, f[Plus[1, x], y]]", e.to_string().as_str());
        println!("Success: {}", *e);
      },

      Err(_) => assert!(false)

    };
  }

  #[test]
  fn precedence_test() {
    let text = "3.8*x^2 + 2*x^f[a+b, c*d, e]";
    let mut parser = Parser::new(text);

    match parser.parse() {

      Ok(e) => {
        assert_eq!(
          "Plus[Times[3.8, Power[x, 2]], Times[2, Power[x, f[Plus[a, b], Times[c, d], e]]]]",
          e.to_string().as_str()
        );
        println!("Success: {}", *e);
      },

      Err(_) => assert!(false)

    };
  }

  #[test]
  fn parentheses_test() {
    let text = "2*(3+a)";
    let mut parser = Parser::new(text);

    match parser.parse() {

      Ok(e) => {
        assert_eq!(
          "Times[2, Plus[3, a]]",
          e.to_string().as_str()
        );
        println!("Success: {}", *e);
      },

      Err(_) => assert!(false)

    };
  }

  #[test]
  /// The parser fixes up artifacts of the parsing process, e.g. "evaluating" `Construct`s, eliding slices, etc.
  fn fixup_test() {
    let text = "a[b, c, d[e, f], g, h]";
    // set_verbosity(5);
    let mut parser = Parser::new(text);

    match parser.parse() {

      Ok(e) => {
        assert_eq!(text, e.to_string());
        println!("Success: {}", *e);
      },

      Err(_) => assert!(false)

    };
  }

}
