{
{-| This lexer internally uses the less-efficient `String` API for @alex@ because
    I can't get the `ByteString` interface to correctly lex unicode symbols.
-}
module Morte.Lexer (
    lexExpr
    ) where

import Data.Text (Text, pack, unpack)
import Morte.Token (Token(..))

}

%wrapper "basic"

$digit = 0-9
$reserved = [\(\)\-\\:→]
$labelchar = $printable # $reserved # $white

tokens :-

    $white+                             ;
    "--".*                              ;
    "("                                 { \bs -> OpenParen        }
    ")"                                 { \bs -> CloseParen       }
    ":"                                 { \bs -> Colon            }
    "@"                                 { \bs -> At               }
    "*"                                 { \bs -> Star             }
    "BOX" | "□"                         { \bs -> Box              }
    "->" | "→"                          { \bs -> Arrow            }
    "\" | "λ" | "L"                     { \bs -> Lambda           }
    "forall" | "|~|" | "\/' | "∀" | "Π" { \bs -> Pi               }
    $digit+                             { \bs -> Number (read bs) }
    $labelchar+                         { \bs -> Label (pack bs)  }

{
-- | Convert a text representation of an expression into a stream of tokens
lexExpr :: Text -> [Token]
lexExpr = alexScanTokens . unpack
}
