module Main where

import Control.Exception (Exception, throwIO)
import Data.Monoid (mempty)
import qualified Data.Text.Lazy.IO as Text
import Morte.Core (typeOf, pretty, normalize)
import Morte.Parser (exprFromText)
import Options.Applicative hiding (Const)
import System.IO (stderr)
import System.Exit (exitFailure)

import Morte.Import (load)

throws :: Exception e => Either e a -> IO a
throws (Left  e) = throwIO e
throws (Right r) = return r

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
    inText   <- Text.getContents
    expr     <- throws (exprFromText inText)
    expr'    <- load expr
    typeExpr <- throws (typeOf expr')
    Text.hPutStrLn stderr (pretty (normalize typeExpr))
    Text.hPutStrLn stderr mempty
    Text.putStrLn (pretty (normalize expr'))
