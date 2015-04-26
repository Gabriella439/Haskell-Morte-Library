{
{-# LANGUAGE OverloadedStrings #-}

-- | Lexing logic for the Morte language
module Morte.Lexer (
    -- * Lexer
    lexExpr,

    -- * Types
    Token(..),
    Position(..)
    ) where

import Control.Monad.Trans.State.Strict (State)
import Data.Bits (shiftR, (.&.))
import Data.Char (ord, digitToInt)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import Data.Word (Word8)
import Lens.Family.State.Strict ((.=), (+=))
import Pipes (Producer, lift, yield)

}

$digit = 0-9

-- Same as Haskell
$opchar = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~]

$fst       = [A-Za-z_]
$labelchar = [A-Za-z0-9_\.]

$whiteNoNewline = $white # \n

tokens :-

    $whiteNoNewline+                    ;
    \n                                  { \_    -> lift (do
                                            line   += 1
                                            column .= 0 )                      }
    "--".*                              ;
    "("                                 { \_    -> yield OpenParen             }
    ")"                                 { \_    -> yield CloseParen            }
    ":"                                 { \_    -> yield Colon                 }
    "@"                                 { \_    -> yield At                    }
    "#"                                 { \_    -> yield Hash                  }
    "*"                                 { \_    -> yield Star                  }
    "BOX" | "□"                         { \_    -> yield Box                   }
    "->" | "→"                          { \_    -> yield Arrow                 }
    "\/" | "|~|" | "forall" | "∀" | "Π" { \_    -> yield Pi                    }
    "\" | "λ"                           { \_    -> yield Lambda                }
    $digit+                             { \text -> yield (Number (toInt text)) }
    $fst $labelchar* | "(" $opchar+ ")" { \text -> yield (Label text)          }

{
toInt :: Text -> Int
toInt = Text.foldl' (\x c -> 10 * x + digitToInt c) 0

-- This was lifted almost intact from the @alex@ source code
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

-- | The cursor's location while lexing the text
data Position = P
    { lineNo    :: {-# UNPACK #-} !Int
    , columnNo  :: {-# UNPACK #-} !Int
    } deriving (Show)

-- line :: Lens' Position Int
line :: Functor f => (Int -> f Int) -> Position -> f Position
line k (P l c) = fmap (\l' -> P l' c) (k l)

-- column :: Lens' Position Int
column :: Functor f => (Int -> f Int) -> Position -> f Position
column k (P l c) = fmap (\c' -> P l c') (k c)

{- @alex@ does not provide a `Text` wrapper, so the following code just modifies
   the code from their @basic@ wrapper to work with `Text`

   I could not get the @basic-bytestring@ wrapper to work; it does not correctly
   recognize Unicode regular expressions.
-}
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

{-| Convert a text representation of an expression into a stream of tokens

    `lexExpr` keeps track of position and returns the remainder of the input if
    lexing fails.
-}
lexExpr :: Text -> Producer Token (State Position) (Maybe Text)
lexExpr text = go (AlexInput '\n' [] text)
  where
    go input = case alexScan input 0 of
        AlexEOF                        -> return Nothing
        AlexError (AlexInput _ _ text) -> return (Just text)
        AlexSkip  input' len           -> do
            lift (column += len)
            go input'
        AlexToken input' len act       -> do
            act (Text.take (fromIntegral len) (currInput input))
            lift (column += len)
            go input'

-- | Token type, used to communicate between the lexer and parser
data Token
    = OpenParen
    | CloseParen
    | Colon
    | At
    | Hash
    | Star
    | Box
    | Arrow
    | Lambda
    | Pi
    | Label Text
    | Number Int
    | EOF
    deriving (Show)
}
