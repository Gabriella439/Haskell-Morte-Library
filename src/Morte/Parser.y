{
{-# LANGUAGE OverloadedStrings #-}

-- | Parsing logic for the Morte language

module Morte.Parser (
    -- * Parser
    exprFromText,

    -- * Errors
    prettyParseError,
    ParseError(..),
    Position(..),
    ParseMessage(..)
    ) where

import Control.Monad.Trans.Error (ErrorT, Error(..), throwError, runErrorT)
import Control.Monad.Trans.State.Strict (State, runState)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Monoid (mempty, (<>))
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Builder as Builder
import Data.Text.Lazy.Builder.Int (decimal)
import Lens.Family.Stock (_1, _2)
import Lens.Family.State.Strict ((.=), use, zoom)
import Morte.Core (Var(..), Const(..), Expr(..))
import qualified Morte.Lexer as Lexer
import Morte.Lexer (Token, Position)
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

Expr :: { Expr }
     : BExpr                                   { $1           }
     | '\\'  '(' VExpr ':' Expr ')' '->' Expr  { Lam $3 $5 $8 }
     | '|~|' '(' VExpr ':' Expr ')' '->' Expr  { Pi  $3 $5 $8 }
     | BExpr '->' Expr                         { Pi "_" $1 $3 }

VExpr :: { Var }
      : label '@' number                       { V $1 $3      }
      | label                                  { V $1 0       }

BExpr :: { Expr }
      :  BExpr AExpr                            { App $1 $2    }
      | AExpr                                  { $1           }

AExpr :: { Expr }
      : VExpr                                  { Var $1       }
      | '*'                                    { Const Star   }
      | 'BOX'                                  { Const Box    }
      | '(' Expr ')'                           { $2           }

{
-- | The specific parsing error
data ParseMessage
    -- | Lexing failed, returning the remainder of the text
    = Lexing Text
    -- | Parsing failed, returning the invalid token
    | Parsing Token
    deriving (Show)

{- This is purely to satisfy the unnecessary `Error` constraint for `ErrorT`

    I will switch to `ExceptT` when the Haskell Platform incorporates
    `transformers-0.4.*`.
-}
instance Error ParseMessage where

type Status = (Position, Producer Token (State Position) (Maybe Text))

type Lex = ErrorT ParseMessage (State Status)

-- To avoid an explicit @mmorph@ dependency
generalize :: Monad m => Identity a -> m a
generalize = return . runIdentity

lexer :: (Token -> Lex a) -> Lex a
lexer k = do
    x <- lift (do
        p <- use _2
        hoist generalize (zoom _1 (next p)) )
    case x of
        Left ml           -> case ml of
            Nothing -> k Lexer.EOF
            Just le -> throwError (Lexing le)
        Right (token, p') -> do
            lift (_2 .= p')
            k token

parseError :: Token -> Lex a
parseError token = throwError (Parsing token)

-- | Parse an `Expr` from `Text` or return a `ParseError` if parsing fails
exprFromText :: Text -> Either ParseError Expr
exprFromText text = case runState (runErrorT parseExpr) initialStatus of
    (x, (position, _)) -> case x of
        Left  e    -> Left (ParseError position e)
        Right expr -> Right expr
  where
    initialStatus = (Lexer.P 1 0, Lexer.lexExpr text)

-- | Structured type for parsing errors
data ParseError = ParseError
    { position     :: Position
    , parseMessage :: ParseMessage
    } deriving (Show)

-- | Pretty-print a `ParseError`
prettyParseError :: ParseError -> Text
prettyParseError (ParseError (Lexer.P l c) e) = Builder.toLazyText (
        "Line:   " <> decimal l <> "\n"
    <>  "Column: " <> decimal c <> "\n"
    <>  "\n"
    <>  case e of
        Lexing r  ->
                "Lexing: \"" <> Builder.fromLazyText remainder <> dots <> "\"\n"
            <>  "\n"
            <>  "Error: Lexing failed\n"
          where
            remainder = Text.takeWhile (/= '\n') (Text.take 64 r)
            dots      = if Text.length r > 64 then "..." else mempty
        Parsing t ->
                "Parsing: " <> Builder.fromString (show t) <> "\n"
            <>  "\n"
            <>  "Error: Parsing failed\n" )
}
