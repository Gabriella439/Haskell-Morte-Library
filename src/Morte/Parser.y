{
{-# LANGUAGE OverloadedStrings #-}

module Morte.Parser (
    parseExpr
    ) where

import Control.Monad.Trans.State.Strict (State, StateT, get, put, evalStateT)
import Data.Text.Lazy (Text)
import Control.Monad.Morph (generalize)
import Lens.Family.Stock (_1, _2)
import Lens.Family.State.Strict (zoom)
import Morte.Core (Var(..), Const(..), Expr(..))
import qualified Morte.Lexer as Lexer
import Morte.Lexer (Token, Position, LexError)
import Pipes (Producer, hoist, lift, next)

}

%name parseExpr
%tokentype { Token }
%monad { Lex }
%lexer { lexer } { Lexer.EOF }
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
data ParseError
    = LexError Lexer.LexError
    | ParseError Lexer.Token
    deriving (Show)

type Status = (Position, Producer Token (State Position) (Maybe LexError))

type Lex = StateT Status (Either ParseError)

lexer :: (Token -> Lex a) -> Lex a
lexer k = do
    p <- zoom _2 get
    x <- hoist generalize (zoom _1 (next p))
    case x of
        Left ml           -> case ml of
            Nothing -> k Lexer.EOF
            Just le -> lift (Left (LexError le))
        Right (token, p') -> do
            zoom _2 (put p')
            k token

parseError :: Token -> Lex a
parseError token = lift (Left (ParseError token))

exprFromText :: Text -> Either ParseError Expr
exprFromText text = evalStateT parseExpr (Lexer.P 0 0, Lexer.lexExpr text)
}
