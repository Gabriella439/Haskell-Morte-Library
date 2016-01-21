module Main where

import Control.Exception (Exception, throwIO)
import Data.Monoid (mempty)
import Data.Traversable
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

data Mode = Default | Resolve | TypeCheck | Normalize

parser :: Parser Mode
parser
    =   subparser
        (   command "resolve"
            (info (helper <*> pure Resolve)
                (   fullDesc
                <>  header "morte resolve - Resolve Morte code"
                <>  progDesc "Transitively replace all remote paths and URLs \
                             \with the code that they refer to, reading the\
                             \program from standard input and writing the \
                             \fully resolved program to standard output."
                )
            )
        <>  metavar "resolve"
        )
    <|> subparser
        (   command "typecheck"
            (   info (helper <*> pure TypeCheck)
                (   fullDesc
                <>  header "morte typecheck - Type-check Morte code"
                <>  progDesc "Verify that Morte code is well-formed by \
                             \type-checking the program, reading the program \
                             \from standard input and writing the program's \
                             \inferred type to standard output."
                ) )
        <>  metavar "typecheck" )
    <|> subparser
        (   command "normalize"
            (   info (helper <*> pure Normalize)
                (   fullDesc
                <>  header "morte normalize - Normalize Morte code"
                <>  progDesc "Reduce Morte code to normal form using \
                             \β-reduction and η-reduction, reading the program \
                             \from standard input and writing the normalized \
                             \program to standard output."
                ) )
        <>  metavar "normalize"
        )
    <|> pure Default

main :: IO ()
main = do
    mode <- execParser $ info (helper <*> parser) 
        (   fullDesc
        <>  header "morte - A bare-bones calculus of constructions"
        <>  progDesc "Type-check, resolve, and normalize a Morte program, \
                     \reading the program from standard input, writing the \
                     \program's normalized type to standard error, and writing \
                     \the normalized program to standard output."
        )
    case mode of
        Default -> do
            inText   <- Text.getContents
            expr     <- throws (exprFromText inText)
            expr'    <- load expr
            typeExpr <- throws (typeOf expr')
            Text.hPutStrLn stderr (pretty (normalize typeExpr))
            Text.hPutStrLn stderr mempty
            Text.putStrLn (pretty (normalize expr'))
        Resolve   -> do
            inText <- Text.getContents
            expr   <- throws (exprFromText inText)
            expr'  <- load expr
            Text.putStrLn (pretty expr')
        TypeCheck -> do
            inText <- Text.getContents
            expr   <- throws (exprFromText inText)
            case traverse (\_ -> Nothing) expr of
                Nothing    -> throwIO (userError
                    "`morte typecheck` cannot type-check a program containing \
                    \remote references.  Use `morte resolve` to resolve all \
                    \remote references or just use `morte` which combines \
                    \resolution, type-checking, and normalization." )
                Just expr' -> do
                    typeExpr <- throws (typeOf expr')
                    Text.putStrLn (pretty typeExpr)
        Normalize -> do
            inText <- Text.getContents
            expr   <- throws (exprFromText inText)
            Text.putStrLn (pretty (normalize expr))
