/*!

An operator is a syntactic component of an expression grammar that may take arguments. The
`Operator` struct holds syntactic data about the operator, which is used by the generic Pratt
parsing algorithm.

A table of operators will hold the operator database for all the operators in the expression
grammar. The parsing algorithm will look up a given operator using the operator's token (sigil).
Thus, the operator table is a `HashMap` from `String` to `Operator`.

*/
#![allow(dead_code)]

use std::collections::HashMap;
use std::fs::File;
use std::io::{BufReader, BufRead};
use crate::ASTNode;
use crate::interpreter::RuntimeContext;

const OPERATOR_DB_FILE: &str = "resources/operators.csv"; // Used in `get_operator_table()`

pub type OperatorTable = HashMap<String, Operator>;

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Associativity {
  Null,  // Things like constants or identifiers that have no affix or associativity. Also,
         // matchfix operators.
  Non,   // The operator cannot be adjacent to another operator of the same precedence.
  Right, // E.g. 2^3^4 == 2^(3^4) != (2^3)^4
  Left,  // E.g. 3-4-5 == (3-4)-5 != 3 - (4-5)
  Full   // Adjacent operators collapse into a single variadic function,
         // e.g. 1 + 2 + 3 + 4 == Plus(1, 2, 3, 4)
}

impl Associativity{
  pub fn from_str(s: &str) -> Associativity {
    match s{

      "R" => Associativity::Right,

      "L" => Associativity::Left,

      "F" => Associativity::Full,

      "N" => Associativity::Non,

      "" => Associativity::Null,

      _ => {unreachable!()}
    }
  }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Affix {
  Null,     // Things like constants or identifiers that have no affix or associativity.
  Prefix,
  Postfix,  // Synonym: suffix (but not used in computer science)
  Infix,
  Matchfix, // Synonyms: circumfix, confix, ambifix

  // More are possible, but these are usually sufficient for most programming languages.
  // Indeed, other linguistic affixes like transfix will be handled by one of the above.
}


impl Affix {
  pub fn from_str(s: &str) -> Affix {
    match s {

      "N" => Affix::Null,

      "P" => Affix::Prefix,

      "S" => Affix::Postfix,

      "I" => Affix::Infix,

      "M" => Affix::Matchfix,

      _   => {unreachable!()}

    }
  }
}


/// An operator has a set of properties that determine how it is parsed. Other properties like commutativity that do
/// not affect how an expression is parsed are not associated with the operator but rather with the function the
/// operator is interpreted as.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct Operator {                // Example Value
  pub name         : String,         // "Multiplication"
  pub precedence   : u32,            // 30
  pub l_token      : Option<String>, // "*"
  pub n_token      : Option<String>, // <None>
  pub o_token      : Option<String>, // <None>
  pub associativity: Associativity,  // "L"
  pub affix        : Affix,          // "I"
  pub arity        : u32,            // 2
}


impl Operator {

  pub fn lbp(&self) -> u32 {
    match self.affix {

      | Affix::Infix
      | Affix::Postfix => self.precedence,

      _ => -1

    }
  }

  pub fn rbp(&self) -> u32 {
    match self.associativity {

      | Associativity::Left
      | Associativity::Non => self.lbp() + 1,

      Associativity::Right => self.lbp(),

      Associativity::Full  => self.lbp() - 1,

      Associativity::Null  => -1 // Technically, Matchfix is N/A.

    }

  }

  pub fn nbp(&self) -> u32 {
    match self.associativity {

      | Associativity::Left
      | Associativity::Right => self.lbp(),

      | Associativity::Non
      | Associativity::Full  => self.lbp() - 1,

      _  => {

        match self.affix {

          Affix::Prefix => self.precedence,
          Affix::Matchfix => 0,
          Affix::Postfix => -1,
          _ => { unreachable!() }
        }
      }

    }
  }

  // The parse-time functionality of `Operator` lives in the `impl Parser`.

}

/*
Reads operator information from a CSV file.

The CSV file is expected to have the following format.

```csv
NAME_STRING, PRECEDENCE, L_TOKEN, N_TOKEN, O_TOKEN, ASSOCIATIVITY, AFFIX, ARITY
Base       , 5         , √      ,        ,        , N            , I    , 2
Power      , 10        , ^      ,        ,        , R            , I    , 2
  ⋮          ⋮            ⋮         ⋮         ⋮       ⋮              ⋮       ⋮
```

Note that the first row is a header row and is discarded.

| Field         | Possible Values                                              | Notes                                                        |
| ------------- | ------------------------------------------------------------ | ------------------------------------------------------------ |
| NAME_STRING   | An identifier as a string                                    | The name is the function the expression will be interpreted as. |
| PRECEDENCE    | Nonnegative integer                                          | The higher the precedence, the stronger the binding power.   |
| L_TOKEN       | String                                                       | A token that accepts an argument on its left                 |
| N_TOKEN       | String                                                       | Null token, a token that appears at the start of an expression |
| O_TOKEN       | String                                                       | Other, a token that is neither an L_TOKEN or an N_TOKEN      |
| ASSOCIATIVITY | "R" - right<br>"L" - left<br>"N" - non<br>"F" - full         | Empty means "null", which is for matchfix operators that have no meaningful notion of associativity. |
| AFFIX         | "N" - Null<br/>"P" - Prefix<br/>"S" - Postfix<br/>"I" - Infix<br/>"M" - Matchfix | As with all strings, quotes are optional.                    |
| ARITY         | Nonnegative integer                                          | How many arguments the expression takes. Consider the ternary operator `a?b:c`. The arity is needed to know whether the `c` belongs with the expression. |

*/
pub fn get_operator_table() -> OperatorTable {
  let f = File::open(OPERATOR_DB_FILE)
      .expect(format!("Could not read from {}", OPERATOR_DB_FILE).as_str());
  let reader = BufReader::new(f);
  let mut operator_table = OperatorTable::new();
  let mut lines = reader.lines();
  lines.next(); // Eat the column headers

  for line in lines {
    let line = line.unwrap();
    let mut fields = line.split(',');

    let new_op = Operator{
      // Fields filled according to csv column order which need not be declaration order.
      name      : fields.next().unwrap().to_string(),
      precedence: fields.next().unwrap().parse::<u32>().unwrap(),
      l_token   : fields.next().map_or(
                    None,
                    |s| if s != "" { Some(s.to_string()) } else { None }
                  ),
      n_token   : fields.next().map_or(
                    None,
                    |s| if s != "" { Some(s.to_string()) } else { None }
                  ),
      o_token   : fields.next().map_or(
                    None,
                    |s| if s != "" { Some(s.to_string()) } else { None }
                  ),
      associativity : Associativity::from_str(fields.next().unwrap()),
      affix     : Affix::from_str(fields.next().unwrap()),
      arity     : fields.next().unwrap().parse::<u32>().unwrap(),

    };

    println!("{:?}", &new_op);
    operator_table.insert(new_op.name.clone(), new_op);
  }

  operator_table
}
