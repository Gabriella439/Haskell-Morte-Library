{
{-# LANGUAGE OverloadedStrings #-}

-- | Lexer logic for the Morte language
module Morte.Lexer (
    -- * Lexer
    Token(..),
    Position(..),
    LexError(..),
    lexExpr
    ) where

import Control.Monad.Trans.State.Strict (State, get, put)
import Data.Bits (shiftR, (.&.))
import Data.Char (ord, digitToInt)
import Data.Monoid (mempty, (<>))
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy.Builder as Builder
import Data.Text.Lazy.Builder.Int (decimal)
import qualified Data.Text.Lazy as Text
import Data.Word (Word8)
import Pipes (Producer, lift, yield)

}

$digit = 0-9
$reserved = [\(\)\-\\:→]
$labelchar = $printable # $reserved # $white
$whiteline = $white # \n

tokens :-

    $whiteline+                         ;
    "\n"                                { \_    -> lift (do
                                            P l c <- get
                                            put (P (l + 1) 0) )                }
    "--".*                              ;
    "("                                 { \_    -> yield OpenParen             }
    ")"                                 { \_    -> yield CloseParen            }
    ":"                                 { \_    -> yield Colon                 }
    "@"                                 { \_    -> yield At                    }
    "*"                                 { \_    -> yield Star                  }
    "BOX" | "□"                         { \_    -> yield Box                   }
    "->" | "→"                          { \_    -> yield Arrow                 }
    "\" | "λ" | "Λ"                     { \_    -> yield Lambda                }
    "forall" | "|~|" | "\/' | "∀" | "Π" { \_    -> yield Pi                    }
    $digit+                             { \text -> yield (Number (toInt text)) }
    $labelchar+                         { \text -> yield (Label text)          }

{
toInt :: Text -> Int
toInt = Text.foldl' (\x c -> 10 * x + digitToInt c) 0

encode :: Char -> (Word8, [Word8])
encode c = (fromIntegral h, map fromIntegral t)
  where
    (h, t) = go (ord c)

    go n
        | n <= 0x7f   = (n, [])
        | n <= 0x7ff  = (0xc0 + (n `shiftR` 6), [0x80 + n .&. 0x3f])
        | n <= 0xffff =
            (   0xe0 + (n `shiftR` 12)
            ,   [   0x80 + ((n `shiftR` 6) .&. 0x3f)
                ,   0x80 + n .&. 0x3f
                ]
            )
        | otherwise   =
            (   0xf0 + (n `shiftR` 18)
            ,   [   0x80 + ((n `shiftR` 12) .&. 0x3f)
                ,   0x80 + ((n `shiftR` 6) .&. 0x3f)
                ,   0x80 + n .&. 0x3f
                ]
            )

data Position = P
    { lineNo    :: {-# UNPACK #-} !Int
    , columnNo  :: {-# UNPACK #-} !Int
    } deriving (Show)

data AlexInput = AlexInput
    { prevChar  :: Char
    , currBytes :: [Word8]
    , currInput :: Text
    }

alexGetByte :: AlexInput -> Maybe (Word8,AlexInput)
alexGetByte (AlexInput c bytes text) = case bytes of
    b:ytes -> Just (b, AlexInput c ytes text)
    []     -> case Text.uncons text of
        Nothing       -> Nothing
        Just (t, ext) -> case encode t of
            (b, ytes) -> Just (b, AlexInput t ytes ext)

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = prevChar

-- | Convert a text representation of an expression into a stream of tokens
lexExpr :: Text -> Producer Token (State Position) (Maybe LexError)
lexExpr text = go (AlexInput '\n' [] text)
  where
    go input = case alexScan input 0 of
        AlexEOF                       -> return Nothing
        AlexError (AlexInput t _ ext) -> do
            P l c <- lift get
            let text = Text.cons t ext
            return (Just (LexError l c text))
        AlexSkip  input' len     -> do
            lift (do
                P l c <- get
                put (P l (c + len)) )
            go input'
        AlexToken input' len act -> do
            lift (do
                P l c <- get
                put (P l (c + len)) )
            act (Text.take (fromIntegral len) (currInput input))
            go input'

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
    | EOF
    deriving (Show)

-- | Structured type for lexical errors
data LexError = LexError
    { line      :: Int
    , column    :: Int
    , remainder :: Text
    } deriving (Show)

-- | Pretty-print a lexical error
prettyLexError :: LexError -> Text
prettyLexError (LexError l c r) = Builder.toLazyText (
        "Line:   " <> decimal l <> "\n"
    <>  "Column: " <> decimal c <> "\n"
    <>  "\n"
    <>  "Remainder: " <> Builder.fromLazyText (Text.take 66 r) <> dots <> "\n"
    <>  "\n"
    <>  "Error: Lexing failed\n" )
  where
    dots = if Text.length r > 66 then "..." else mempty
}
