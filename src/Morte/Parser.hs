{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo       #-}

-- | Parsing logic for the Morte language

module Morte.Parser (
    -- * Parser
    exprFromText,

    -- * Errors
    ParseError(..),
    ParseMessage(..)
    ) where

import Control.Applicative hiding (Const)
import Control.Exception (Exception)
import Control.Monad.Trans.Class  (lift)
import Control.Monad.Trans.Except (Except, throwE, runExceptT)
import Control.Monad.Trans.State.Strict (evalState, get)
import Data.Monoid
import Data.Text.Buildable (Buildable(..))
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder (toLazyText)
import Data.Typeable (Typeable)
import Filesystem.Path.CurrentOS (FilePath)
import Morte.Core (Var(..), Const(..), Path(..), Expr(..))
import Morte.Lexer (LocatedToken(..), Position(..), Token)
import Prelude hiding (FilePath)
import Text.Earley

import qualified Morte.Lexer    as Lexer
import qualified Pipes.Prelude  as Pipes
import qualified Data.Text.Lazy as Text

match :: Token -> Prod r Token LocatedToken Token
match t = fmap Lexer.token (satisfy predicate) <?> t
  where
    predicate (LocatedToken t' _) = t == t'

label :: Prod r e LocatedToken Text
label = fmap unsafeFromLabel (satisfy isLabel)
  where
    isLabel (LocatedToken (Lexer.Label _) _) = True
    isLabel  _                               = False

    unsafeFromLabel (LocatedToken (Lexer.Label l) _) = l

number :: Prod r e LocatedToken Int
number = fmap unsafeFromNumber (satisfy isNumber)
  where
    isNumber (LocatedToken (Lexer.Number _) _) = True
    isNumber  _                                = False

    unsafeFromNumber (LocatedToken (Lexer.Number n) _) = n

file :: Prod r e LocatedToken FilePath
file = fmap unsafeFromFile (satisfy isFile)
  where
    isFile (LocatedToken (Lexer.File _) _) = True
    isFile  _                              = False

    unsafeFromFile (LocatedToken (Lexer.File n) _) = n

url :: Prod r e LocatedToken String
url = fmap unsafeFromURL (satisfy isURL)
  where
    isURL (LocatedToken (Lexer.URL _) _) = True
    isURL  _                             = False

    unsafeFromURL (LocatedToken (Lexer.URL n) _) = n

expr :: Grammar r (Prod r Token LocatedToken (Expr Path))
expr = mdo
    expr <- rule
        (   bexpr
        <|> (   Lam
            <$> (match Lexer.Lambda *> match Lexer.OpenParen *> label)
            <*> (match Lexer.Colon *> expr)
            <*> (match Lexer.CloseParen *> match Lexer.Arrow *> expr)
            )
        <|> (   Pi
            <$> (match Lexer.Pi *> match Lexer.OpenParen *> label)
            <*> (match Lexer.Colon *> expr)
            <*> (match Lexer.CloseParen *> match Lexer.Arrow *> expr)
            )
        <|> (   Pi "_"
            <$> bexpr
            <*> (match Lexer.Arrow *> expr)
            )
        )
    vexpr <- rule
        (   (   V
            <$> label
            <*> (match Lexer.At *> number)
            )
        <|> (   V
            <$> label
            <*> pure 0
            )
        )
    bexpr <- rule
        (   (   App
            <$> bexpr
            <*> aexpr
            )
        <|> aexpr
        )
    aexpr <- rule
        (   (   Var
            <$> vexpr
            )
        <|> (   match Lexer.Star *> pure (Const Star)
            )
        <|> (   match Lexer.Box  *> pure (Const Box)
            )
        <|> (   Embed
            <$> import_
            )
        <|> (   match Lexer.OpenParen *> expr <* match Lexer.CloseParen
            )
        )

    import_ <- rule
        (   (   File
            <$> file
            )
        <|> (   URL
            <$> url
            )
        )

    return expr

-- | The specific parsing error
data ParseMessage
    -- | Lexing failed, returning the remainder of the text
    = Lexing Text
    -- | Parsing failed, returning the invalid token and the expected tokens
    | Parsing Token [Token]
    deriving (Show)

-- | Structured type for parsing errors
data ParseError = ParseError
    { position     :: Position
    , parseMessage :: ParseMessage
    } deriving (Typeable)

instance Show ParseError where
    show = Text.unpack . toLazyText . build

instance Exception ParseError

instance Buildable ParseError where
    build (ParseError (Lexer.P l c) e) =
            "\n"
        <>  "Line:   " <> build l <> "\n"
        <>  "Column: " <> build c <> "\n"
        <>  "\n"
        <>  case e of
            Lexing r                                     ->
                    "Lexing: \"" <> build remainder <> dots <> "\"\n"
                <>  "\n"
                <>  "Error: Lexing failed\n"
              where
                remainder = Text.takeWhile (/= '\n') (Text.take 64 r)
                dots      = if Text.length r > 64 then "..." else mempty
            Parsing t ts ->
                    "Parsing : " <> build (show t ) <> "\n"
                <>  "Expected: " <> build (show ts) <> "\n"
                <>  "\n"
                <>  "Error: Parsing failed\n"

-- | Parse an `Expr` from `Text` or return a `ParseError` if parsing fails
exprFromText :: Text -> Either ParseError (Expr Path)
exprFromText text = evalState (runExceptT m) (Lexer.P 1 0)
  where
    m = do
        (locatedTokens, mtxt) <- lift (Pipes.toListM' (Lexer.lexExpr text))
        case mtxt of
            Nothing  -> return ()
            Just txt -> do
                pos <- lift get
                throwE (ParseError pos (Lexing txt))
        let (parses, Report _ needed found) =
                fullParses (parser expr) locatedTokens
        case parses of
            parse:_ -> return parse
            []      -> do
                let LocatedToken t pos = case found of
                        lt:_ -> lt
                        _    -> LocatedToken Lexer.EOF (P 0 0)
                throwE (ParseError pos (Parsing t needed))
