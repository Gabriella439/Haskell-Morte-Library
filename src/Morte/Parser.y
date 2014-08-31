{
{-# LANGUAGE OverloadedStrings #-}

module Morte.Parser (
    parseExpr
    ) where

import Data.Text (Text)
import qualified Morte.Lexer as Lexer
import Morte.Core (Var(..), Const(..), Expr(..))
}

%name parseExpr
%tokentype { Lexer.Token }
%monad { Either String }
%error { parseError }

%token
    '('    { Lexer.OpenParen  }
    ')'    { Lexer.CloseParen }
    ':'    { Lexer.Colon      }
    '@'    { Lexer.At         }
    '*'    { Lexer.Star       }
    'BOX'  { Lexer.Box        }
    '->'   { Lexer.Arrow      }
    '\\'   { Lexer.Lambda     }
    '|~|'  { Lexer.Pi         }
    label  { Lexer.Label $$   }
    number { Lexer.Number $$  }

%%

Expr : BExpr                                    { $1           }
     | '\\'  '(' VExpr ':' AExpr ')' '->' Expr  { Lam $3 $5 $8 }
     | '|~|' '(' VExpr ':' AExpr ')' '->' Expr  { Pi  $3 $5 $8 }
     | BExpr '->' Expr                          { Pi "_" $1 $3 }

VExpr : label '@' number                        { V $1 $3      }
      | label                                   { V $1 0       }

BExpr : BExpr AExpr                             { App $1 $2    }
      | AExpr                                   { $1           }

AExpr : VExpr                                   { Var $1       }
      | '*'                                     { Const Star   }
      | 'BOX'                                   { Const Box    }

{
parseError :: [Lexer.Token] -> Either String a
parseError _ = Left "Expression parsing failed"
}
