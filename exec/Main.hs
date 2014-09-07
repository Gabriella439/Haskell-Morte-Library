module Main where

import qualified Data.Text.Lazy.IO as Text
import Morte.Core (typeOf, prettyTypeError, prettyExpr, normalize)
import Morte.Parser (exprFromText, prettyParseError)
import Options.Applicative
import System.IO (stderr)

main :: IO ()
main = do
    execParser $ info (helper <*> pure ())
        (   fullDesc
        <>  header "morte - A bare-bones calculus of constructions"
        <>  progDesc "Type-check and normalize a Morte program, reading the \
                     \program from standard input, writing the program's type \
                     \to standard error, and writing the normalized program to\
                     \standard output"
        )
    inText <- Text.getContents
    case exprFromText inText of
        Left  pe   -> Text.hPutStr stderr (prettyParseError pe)
        Right expr -> case typeOf expr of
            Left  te       -> Text.hPutStr stderr (prettyTypeError te)
            Right typeExpr -> do
                Text.hPutStrLn stderr (prettyExpr (normalize typeExpr))
                Text.putStrLn (prettyExpr (normalize expr))
