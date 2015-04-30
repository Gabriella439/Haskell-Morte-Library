module Main where

import Data.Monoid (mempty)
import qualified Data.Text.Lazy.IO as Text
import Morte.Core (typeOf, prettyTypeError, prettyExpr, normalize)
import Morte.Parser (exprFromText, prettyParseError)
import Options.Applicative hiding (Const)
import System.IO (stderr)
import System.Exit (exitFailure)

import Morte.Import (load)

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
        Left  pe   -> do
            Text.hPutStr stderr (prettyParseError pe)
            exitFailure
        Right expr -> do
            expr' <- load expr
            case typeOf expr' of
                Left  te       -> do
                    Text.hPutStr stderr (prettyTypeError te)
                    exitFailure
                Right typeExpr -> do
                    Text.hPutStrLn stderr (prettyExpr (normalize typeExpr))
                    Text.hPutStrLn stderr mempty
                    Text.putStrLn (prettyExpr (normalize expr'))
