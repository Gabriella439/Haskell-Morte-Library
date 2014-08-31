{-| Shared token type for the @alex@-generated lexer and the @happy@-generated
    parser
-}

module Morte.Token (
    Token(..)
    ) where

import Data.Text (Text)

-- | Token type, used to communicate between the lexer and parser
data Token
    = OpenParen
    | CloseParen
    | Colon
    | At
    | Star
    | Box
    | Arrow
    | Lambda
    | Pi
    | Label Text
    | Number Int
    deriving (Show)
