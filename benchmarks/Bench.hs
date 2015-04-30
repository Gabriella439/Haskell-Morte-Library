module Main (main) where

import Morte.Core
import Morte.Import (load)
import Morte.Parser (ParseError, exprFromText, prettyParseError)

import Control.Monad     (foldM)
import Criterion.Main    (Benchmark, defaultMain, env, bgroup, bench, nf)
import Data.Text.Lazy    (Text)
import qualified Data.Text.Lazy as T
import Data.Text.Lazy.IO (readFile, hPutStrLn)
import GHC.IO.Handle.FD  (stderr)
import Paths_morte       (getDataFileName)
import Prelude hiding    (readFile)

benchFilenames :: [String]
benchFilenames = [
      "recursive.mt"
    , "factorial.mt"
    ]

readMtFile :: String -> IO (String, Text)
readMtFile filename = do
    path   <- getDataFileName filename
    mtFile <- readFile path
    return (filename, mtFile)

partitionExpr
    :: ([(String, ParseError)],[(String, Expr X)])
    -> (String, Text)
    -> IO ([(String, ParseError)],[(String, Expr X)])
partitionExpr (pe, ps) (filename, contents) =
    case exprFromText contents of
        Left  perr -> return ((filename,perr):pe,ps)
        Right expr -> do
            expr' <- load expr
            return (pe,(filename,expr'):ps)

pprFileParseError :: (String, ParseError) -> Text
pprFileParseError (fn,pe) = T.unlines [T.pack fn, prettyParseError pe]

srcEnv :: IO [(String, Expr X)]
srcEnv = do
    mtFiles <- mapM readMtFile benchFilenames
    (pe,ps) <- foldM partitionExpr ([],[]) mtFiles
    mapM_ (hPutStrLn stderr . pprFileParseError) pe
    return ps

main :: IO ()
main = defaultMain [
      env srcEnv $ bgroup "source" . map benchExpr
    ]

benchExpr :: (String, Expr X) -> Benchmark
benchExpr (tag,expr) = bgroup tag [
      bench "normalize" $ nf normalize expr
    , bench "equality"  $ nf (expr ==) expr
    , bench "typeOf"    $ nf typeOf    expr
    ]
