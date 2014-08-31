{
module Morte.Parser (
    parseExpr
    ) where

import Data.Text (Text)
import Morte.Lexer (Token(..))
}

%name parseExpr
%tokentype { Token }
%error { parseError }

%token
    '('    { OpenParen  }
    ')'    { CloseParen }
    ':'    { Colon      }
    '@'    { At         }
    '*'    { Star       }
    'BOX'  { Box        }
    '->'   { Arrow      }
    '\\'   { Lambda     }
    '|~|'  { Pi         }
    label  { Label $$   }
    number { Number $$  }

%%

Expr : BExpr                                    { Expr1 $1       }
     | '\\'  '(' VExpr ':' AExpr ')' '->' Expr  { Expr2 $3 $5 $8 }
     | '|~|' '(' VExpr ':' AExpr ')' '->' Expr  { Expr3 $3 $5 $8 }
     | BExpr '->' Expr                          { Expr4 $1 $3    }

VExpr : label '@' number                        { VExpr1 $1 2    }
      | label                                   { VExpr2 $1      }

BExpr : BExpr AExpr                             { BExpr1 $1 $2   }
      | AExpr                                   { BExpr2 $1      }

AExpr : VExpr                                   { AExpr1 $1      }
      | '*'                                     { AExpr2         }
      | 'BOX'                                   { AExpr3         }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"

data Expr
    = Expr1 BExpr
    | Expr2 VExpr AExpr Expr
    | Expr3 VExpr AExpr Expr
    | Expr4 BExpr Expr
    deriving (Show)

data BExpr
    = BExpr1 BExpr AExpr
    | BExpr2 AExpr
    deriving (Show)

data AExpr
    = AExpr1 VExpr
    | AExpr2
    | AExpr3
    deriving (Show)

data VExpr = VExpr1 Text Int | VExpr2 Text
    deriving (Show)
}
