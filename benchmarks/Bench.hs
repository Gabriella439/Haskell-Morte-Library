{-# LANGUAGE OverloadedStrings #-}

import Control.Exception (throwIO)
import Criterion.Main (Benchmark, defaultMain, env, bgroup, bench, nf)
import Filesystem.Path.CurrentOS (FilePath)
import Morte.Core (Expr, X)
import Paths_morte (getDataFileName)
import Prelude hiding (FilePath)

import qualified Data.Text.Lazy.IO         as Text
import qualified Filesystem.Path.CurrentOS as Filesystem
import qualified Morte.Core                as Morte
import qualified Morte.Import              as Morte
import qualified Morte.Parser              as Morte

readMorteFile :: FilePath -> IO (Expr X)
readMorteFile filename = do
    str <- getDataFileName (Filesystem.encodeString filename)
    text <- Text.readFile str
    case Morte.exprFromText text of
        Left  e    -> throwIO e
        Right expr -> Morte.load expr

main :: IO ()
main = defaultMain
    [ env srcEnv (\ ~(x0, x1) ->
        bgroup "source"
            [ benchExpr "recursive.mt" x0
            , benchExpr "factorial.mt" x1
            ] )
    ]
  where
    srcEnv = do
        x0 <- readMorteFile "recursive.mt"
        x1 <- readMorteFile "factorial.mt"
        return (x0, x1)

benchExpr :: FilePath -> Expr X -> Benchmark
benchExpr path expr = bgroup (Filesystem.encodeString path)
    [ bench "normalize" (nf Morte.normalize expr)
    , bench "equality"  (nf (expr ==)       expr)
    , bench "typeOf"    (nf Morte.typeOf    expr)
    ]
