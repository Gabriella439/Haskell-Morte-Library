module Main where

import Control.Applicative (empty)
import Data.Monoid (mempty)
import Data.Void (Void)
import qualified Data.Text.Lazy.IO as Text
import Morte.Core (typeOf, prettyTypeError, prettyExpr, normalize)
import Morte.Parser (exprFromText, prettyParseError)
import Options.Applicative hiding (Const)
import System.IO (stderr)
import System.Exit (exitFailure)

import Morte.Core (Expr(..), Path)

closed :: Expr Path -> Maybe (Expr Void)
closed (Const c    ) = pure (Const c)
closed (Var   v    ) = pure (Var   v)
closed (Lam x _A  b) = Lam x <$> closed _A <*> closed  b
closed (Pi  x _A _B) = Pi  x <$> closed _A <*> closed _B
closed (App f a    ) = App <$> closed f <*> closed a
closed (Import _   ) = empty

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
        Right expr -> case closed expr of
            Just expr' -> case typeOf expr' of
                Left  te       -> do
                    Text.hPutStr stderr (prettyTypeError te)
                    exitFailure
                Right typeExpr -> do
                    Text.hPutStrLn stderr (prettyExpr (normalize typeExpr))
                    Text.hPutStrLn stderr mempty
                    Text.putStrLn (prettyExpr (normalize expr'))
