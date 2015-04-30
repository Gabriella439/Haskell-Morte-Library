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
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as Lazy
import Data.Char (ord, digitToInt)
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Encoding (encodeUtf8)
import qualified Data.Text.Lazy as Text
import Data.Word (Word8)
import Filesystem.Path.CurrentOS (FilePath, fromText)
import Lens.Family.State.Strict ((.=), (+=))
import Pipes (Producer, lift, yield)
import Prelude hiding (FilePath)

}

$digit = 0-9

-- Same as Haskell
$opchar = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~]

$fst        = [A-Za-z_]
$labelchar  = [A-Za-z0-9_]
$domainchar = [A-Za-z0-9\.]
$pathchar   = [A-Za-z0-9\.\/]

$whiteNoNewline = $white # \n

tokens :-

    $whiteNoNewline+                    ;
    \n                                  { \_    -> lift (do
                                            line   += 1
                                            column .= 0 )                     }
    "--".*                              ;
    "("                                 { \_    -> yield OpenParen            }
    ")"                                 { \_    -> yield CloseParen           }
    ":"                                 { \_    -> yield Colon                }
    "*"                                 { \_    -> yield Star                 }
    "BOX" | "□"                         { \_    -> yield Box                  }
    "->" | "→"                          { \_    -> yield Arrow                }
    "\/" | "|~|" | "forall" | "∀" | "Π" { \_    -> yield Pi                   }
    "\" | "λ"                           { \_    -> yield Lambda               }
    $fst $labelchar* | "(" $opchar+ ")" { \text -> yield (Label text)         }
    "#" $pathchar+                      { \text -> yield (File (toFile text)) }
    "@" $digit+                         { \text -> yield (At (toAt text))     }
    "@" $domainchar+                    { \text -> yield (Host (toHost text)) }
    ":" $digit+                         { \text -> yield (Port (toPort text)) }
    "/" $pathchar+                      { \text -> yield (Path (toPath text)) }

{
toInt :: Text -> Int
toInt = Text.foldl' (\x c -> 10 * x + digitToInt c) 0

toAt :: Text -> Int
toAt = toInt . Text.drop 1

toPort :: Text -> Int
toPort = toInt . Text.drop 1

toHost :: Text -> ByteString
toHost = Lazy.toStrict . encodeUtf8 . Text.drop 1

toPath :: Text -> ByteString
toPath = Lazy.toStrict . encodeUtf8 . Text.drop 1

toFile :: Text -> FilePath
toFile = fromText . Text.toStrict . Text.drop 1

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
    | At Int
    | Star
    | Box
    | Arrow
    | Lambda
    | Pi
    | Label Text
    | Host ByteString
    | Port Int
    | Path ByteString
    | File FilePath
    | EOF
    deriving (Show)
}
