module Main where

import Control.Exception (Exception, throwIO)
import Data.Monoid (mempty)
import qualified Data.Text.Lazy.IO as Text
import Morte.Core (Expr(..), Path(..), typeOf, pretty, normalize)
import Options.Applicative hiding (Const)
import System.IO (stderr)
import System.Exit (exitFailure)

import Morte.Import (load)

throws :: Exception e => Either e a -> IO a
throws (Left  e) = throwIO e
throws (Right r) = return r

parser :: Parser String
parser = strArgument
    (   metavar "ADDRESS"
    <>  help "An IPFS address pointing to a Morte expression"
    )

main :: IO ()
main = do
    address <- execParser $ info (helper <*> parser)
        (   fullDesc
        <>  header "morte-ipfs - Invoke `morte` on a given IPFS address"
        <>  progDesc "Type-check, normalize, and display a Morte program read \
                     \from an IPFS address."
        )
    let expr = Embed (URL ("https://ipfs.io:8080/" ++ address))
    expr'    <- load expr
    typeExpr <- throws (typeOf expr')
    Text.hPutStrLn stderr (pretty (normalize typeExpr))
    Text.hPutStrLn stderr mempty
    Text.putStrLn (pretty (normalize expr'))
