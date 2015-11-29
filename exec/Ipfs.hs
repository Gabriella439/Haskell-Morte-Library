module Main where

import Control.Exception (Exception, throwIO)
import Data.Monoid (mempty)
import qualified Data.Text.Lazy.IO as Text
import Data.List (isInfixOf)
import Morte.Core (Expr(..), Path(..), typeOf, pretty, normalize)
import Options.Applicative hiding (Const)
import System.IO (stderr)
import System.Exit (exitFailure)

import Morte.Import (load)

throws :: Exception e => Either e a -> IO a
throws (Left  e) = throwIO e
throws (Right r) = return r

data Options = Options
    { address :: String
    , gateway :: String
    , service :: String
    }

parser :: Parser Options
parser =
        Options
    <$> strArgument
        (   metavar "ADDRESS"
        <>  help "An IPFS address or hash pointing to a Morte expression"
        )
    <*> strOption
        (   long "host"
        <>  short 'h'
        <>  metavar "HOST"
        <>  help "The IPFS gateway server"
        <>  value "gateway.ipfs.io"
        <>  showDefaultWith id
        )
    <*> strOption
        (   long "port"
        <>  short 'p'
        <>  metavar "PORT"
        <>  help "Port or service to connect on"
        <>  value "8080"
        <>  showDefault
        )

main :: IO ()
main = do
    Options address host port <- execParser $ info (helper <*> parser)
        (   fullDesc
        <>  header "morte-ipfs - Invoke `morte` on a given IPFS address"
        <>  progDesc "Type-check, normalize, and display a Morte program read \
                     \from an IPFS address or hash."
        )
    if isInfixOf "/ipfs/" address 
        then let expr = Embed (URL ("http://" ++ host ++ ":" ++ port ++ address))
        else let expr = Embed (URL ("http://" ++ host ++ ":" ++ port ++ "/ipfs/" ++ address))
    expr'    <- load expr
    typeExpr <- throws (typeOf expr')
    Text.hPutStrLn stderr (pretty (normalize typeExpr))
    Text.hPutStrLn stderr mempty
    Text.putStrLn (pretty (normalize expr'))