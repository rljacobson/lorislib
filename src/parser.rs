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

use crate::{
  operator::*,
  atoms::{
    Function,
    Integer,
    Real,
    Sequence,
    SequenceVariable,
    StringLiteral,
    Symbol,
    Variable,
  },
  expression::{
    Expression,
    RcExpression
  },
};


const INF: u32 = u32::MAX;

pub struct Parser<'s> {
  pub op_table : OperatorTable,
  pub root_node: Option<RcExpression>,
  text         : &'s str,
  cursor       : u32,
}

impl<'s> Parser<'s> {

  pub fn new(text: &str) -> Parser {
    // Load operator database
    let op_table = OperatorTable::new();

    Parser{
      op_table,
      root_node: None,
      text,
      cursor: 0
    }
  }


  pub fn parse(text: &str) -> Option<RcExpression>{
    // Bootstrap parsing algorithm...
    None
  }

  #[allow(non_snake_case)]
  fn E(&self, p: u32){
    let mut token = self.consume();

    let c = null_command_lookup(token);
    let tree = c.null_denotation(terminal); // = c(terminal)
    let mut r: u32 = INF;

    loop {
      token = self.get_current_token();
      // Look up the node class of the expression we are currently parsing
      // based on the value of token. The node class knows it's left and
      // next binding power.
      c = self.left_command_lookup(token.type);
      if (p > c.left_binding_power ) || (c.left_binding_power() > r) {
        break;
      }

      self.consume();
      let terminal = TerminalNodeImpl(token);

      // Make the node
      tree = c.left_denotation(self, tree, terminal); // = c(tree, terminal)
      r = c.next_binding_power();
    }

    return tree;

  }

  fn left_command_lookup(&self, ttype: u32) -> ASTNode {
    // Returns the node class for token type ttype.
    self.left_command_table.get(ttype, DefaultLeftCommand)
  }

  fn null_command_lookup(&self, ttype: u32) -> ASTNode {
    self.null_command_table.get(ttype, DefaultNullCommand)
  }

  /// The lexer.
  fn next_token(&self) -> ASTNode {
    ASTNode::Terminal("thisisaterminal")
  }

  /// NBP stands for the "next binding power". It gives the highest precedence of the operator that
  /// this operator can be a left operand of.
  pub fn next_binding_power(&self) -> u32 {
    return -1;
  }

  pub fn right_binding_power(&self) -> u32 {
    return -1;
  }

  /// LBP stands for "left binding power". It replaces the prec table. L
  /// tokens will have a nonnegative LBP, while all others have an LBP of
  ///  -1.
  pub fn left_binding_power(&self) -> u32 {
    return -1;
  }

}
