{-# LANGUAGE OverloadedStrings #-}

module Main (
    main
  ) where

import Control.Exception (throwIO)
import ClosedWellTyped (ClosedWellTyped(..))
import Data.Text.Lazy (Text)
import Filesystem.Path (FilePath)
import Morte.Core (Expr, X)
import Paths_morte (getDataFileName)
import Prelude hiding (FilePath)
import Test.Tasty (TestTree)

import qualified Data.Text.Lazy.IO         as Text
import qualified Filesystem.Path.CurrentOS as Filesystem
import qualified Morte.Core                as Morte
import qualified Morte.Import              as Morte
import qualified Morte.Parser              as Morte
import qualified Test.Tasty                as Tasty
import qualified Test.Tasty.QuickCheck     as QuickCheck
import qualified Test.Tasty.HUnit          as HUnit

main :: IO ()
main = Tasty.defaultMain tests

tests :: TestTree
tests =
    Tasty.testGroup "Tests"
        [ Tasty.testGroup "Properties"
            [ QuickCheck.testProperty "Normalization is idempotent"
                normalizationIsIdempotent 
            , QuickCheck.testProperty "Normalization preserves type safety"
                normalizationPreservesTypeSafety
            ]
        , Tasty.testGroup "Unit tests"
            [ HUnit.testCase "Tutorial - Identity"           example0
            , HUnit.testCase "Tutorial - id.mt"              example1
            , HUnit.testCase "Tutorial - id2.mt"             example2
            , HUnit.testCase "Tutorial - bool.mt"            example3
            , HUnit.testCase "Tutorial - pair.mt"            example4
            , HUnit.testCase "Tutorial - all.mt"             example5
            , HUnit.testCase "Tutorial - mapid1.mt"          example6
            , HUnit.testCase "Tutorial - mapid2.mt"          example7
            , HUnit.testCase "Tutorial - mapcomp1.mt"        example8
            , HUnit.testCase "Tutorial - mapcomp2.mt"        example9
            , HUnit.testCase "Tutorial - corecursive.mt - A" example10
            , HUnit.testCase "Tutorial - corecursive.mt - B" example11
            , HUnit.testCase "Tutorial - corecursive.mt - C" example12
            , HUnit.testCase "Tutorial - corecursive.mt - D" example13
            , HUnit.testCase "Tutorial - recursive.mt"       example14
            , HUnit.testCase "Tutorial - corecursive.mt"     example15
            ]
        ]

typeChecks :: Expr X -> Bool
typeChecks expr = case Morte.typeOf expr of
    Right _ -> True
    Left  _ -> False

-- Carefully note that `ClosedWellTyped` generates well-typed expressions, so
-- this is really testing that `typeChecks expr ==> typeChecks (normalize expr)`
normalizationPreservesTypeSafety :: ClosedWellTyped -> Bool
normalizationPreservesTypeSafety (ClosedWellTyped expr) =
    typeChecks (Morte.normalize expr)

-- Carefully note that `(==)` also normalizes both sides before checking for
-- α-equality, so this is really testing that `normalize (normalize expr)` and
-- `normalize expr` are α-equivalent.
normalizationIsIdempotent :: ClosedWellTyped -> Bool
normalizationIsIdempotent (ClosedWellTyped expr) = Morte.normalize expr == expr

example
    :: FilePath
    -> Text
    -> Text
    -> IO ()
example path stderr stdout = do
    str   <- getDataFileName (Filesystem.encodeString path)
    stdin <- Text.readFile str
    case Morte.exprFromText stdin of
        Left  e    -> throwIO e
        Right expr -> do
            expr' <- Morte.load expr
            case Morte.typeOf expr' of
                Left  e        -> throwIO e
                Right typeExpr -> do
                    let stderr' = Morte.pretty (Morte.normalize typeExpr)
                    let stdout' = Morte.pretty (Morte.normalize expr')
                    HUnit.assertEqual "" stderr stderr'
                    HUnit.assertEqual "" stdout stdout'

example0 :: IO ()
example0 =
    example
        "test/src/example0.mt"
        "∀(a : *) → ∀(x : a) → a"
        "λ(a : *) → λ(x : a) → x"

example1 :: IO ()
example1 =
    example
        "test/src/example1.mt"
        "∀(String : *) → ∀(x : String) → String"
        "λ(String : *) → λ(x : String) → x"

example2 :: IO ()
example2 =
    example
        "test/src/example2.mt"
        "∀(a : *) → a → a"
        "λ(a : *) → λ(x : a) → x"

example3 :: IO ()
example3 =
    example
        "test/src/example3.mt"
        "∀(Int : *) → ∀(Zero : Int) → ∀(One : Int) → Int"
        "λ(Int : *) → λ(Zero : Int) → λ(One : Int) → One"

example4 :: IO ()
example4 =
    example
        "test/src/example4.mt"
        "∀(a : *) → ∀(x : a) → ∀(y : a) → a"
        "λ(a : *) → λ(x : a) → λ(y : a) → y"

example5 :: IO ()
example5 =
    example
        "test/src/example5.mt"
        "∀(r : *) → r → r → r"
        "λ(r : *) → λ(x : r) → λ(_ : r) → x"

example6 :: IO ()
example6 =
    example
        "test/src/example6.mt"
        "∀(a : *) → (∀(x : *) → (a → x → x) → x → x) → ∀(x : *) → (a → x → x) → x → x"
        "λ(a : *) → λ(l : ∀(x : *) → (a → x → x) → x → x) → l"

example7 :: IO ()
example7 =
    example
        "test/src/example7.mt"
        "∀(a : *) → (∀(x : *) → (a → x → x) → x → x) → ∀(x : *) → (a → x → x) → x → x"
        "λ(a : *) → λ(va : ∀(x : *) → (a → x → x) → x → x) → va"

example8 :: IO ()
example8 =
    example
        "test/src/example8.mt"
        "∀(a : *) → ∀(b : *) → ∀(c : *) → ∀(f : b → c) → ∀(g : a → b) → (∀(x : *) → (a → x → x) → x → x) → ∀(x : *) → (c → x → x) → x → x"
        "λ(a : *) → λ(b : *) → λ(c : *) → λ(f : b → c) → λ(g : a → b) → λ(l : ∀(x : *) → (a → x → x) → x → x) → λ(x : *) → λ(Cons : c → x → x) → l x (λ(va : a) → Cons (f (g va)))"

example9 :: IO ()
example9 =
    example
        "test/src/example9.mt"
        "∀(a : *) → ∀(b : *) → ∀(c : *) → ∀(f : b → c) → ∀(g : a → b) → (∀(x : *) → (a → x → x) → x → x) → ∀(x : *) → (c → x → x) → x → x"
        "λ(a : *) → λ(b : *) → λ(c : *) → λ(f : b → c) → λ(g : a → b) → λ(va : ∀(x : *) → (a → x → x) → x → x) → λ(x : *) → λ(Cons : c → x → x) → va x (λ(va : a) → Cons (f (g va)))"

example10 :: IO ()
example10 =
    example
        "test/src/example10.mt"
        "∀(a : *) → (∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x"
        "λ(a : *) → λ(st : ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → st"

example11 :: IO ()
example11 =
    example
        "test/src/example11.mt"
        "∀(a : *) → (∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x"
        "λ(a : *) → λ(va : ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → va"

example12 :: IO ()
example12 =
    example
        "test/src/example12.mt"
        "∀(a : *) → ∀(b : *) → ∀(c : *) → (b → c) → (a → b) → (∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (c → s → x) → x) → x) → x"
        "λ(a : *) → λ(b : *) → λ(c : *) → λ(f : b → c) → λ(g : a → b) → λ(st : ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → λ(x : *) → λ(S : ∀(s : *) → s → (s → ∀(x : *) → (c → s → x) → x) → x) → st x (λ(s : *) → λ(seed : s) → λ(step : s → ∀(x : *) → (a → s → x) → x) → S s seed (λ(seed : s) → λ(x : *) → λ(Pair : c → s → x) → step seed x (λ(va : a) → Pair (f (g va)))))"

example13 :: IO ()
example13 =
    example
        "test/src/example13.mt"
        "∀(a : *) → ∀(b : *) → ∀(c : *) → (b → c) → (a → b) → (∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (c → s → x) → x) → x) → x"
        "λ(a : *) → λ(b : *) → λ(c : *) → λ(f : b → c) → λ(g : a → b) → λ(va : ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → λ(x : *) → λ(S : ∀(s : *) → s → (s → ∀(x : *) → (c → s → x) → x) → x) → va x (λ(s : *) → λ(seed : s) → λ(step : s → ∀(x : *) → (a → s → x) → x) → S s seed (λ(seed : s) → λ(x : *) → λ(Pair : c → s → x) → step seed x (λ(va : a) → Pair (f (g va)))))"

example14 :: IO ()
example14 =
    example
        "test/src/example14.mt"
        "∀(String : *) → ∀(U : *) → ∀(Unit : U) → ∀(x : *) → (String → x → x) → ((String → x) → x) → (U → x) → x"
        "λ(String : *) → λ(U : *) → λ(Unit : U) → λ(x : *) → λ(PutStrLn : String → x → x) → λ(GetLine : (String → x) → x) → λ(Return : U → x) → GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (Return Unit))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"

example15 :: IO ()
example15 =
    example
        "test/src/example15.mt"
        "∀(String : *) → ∀(r : *) → ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (String → s → x) → ((String → s) → x) → (r → x) → x) → x) → x"
        "λ(String : *) → λ(r : *) → λ(x : *) → λ(k : ∀(s : *) → s → (s → ∀(x : *) → (String → s → x) → ((String → s) → x) → (r → x) → x) → x) → k (∀(x : *) → (String → x) → x → x) (λ(x : *) → λ(Just : String → x) → λ(Nothing : x) → Nothing) (λ(m : ∀(x : *) → (String → x) → x → x) → m (∀(x : *) → (String → (∀(x : *) → (String → x) → x → x) → x) → ((String → ∀(x : *) → (String → x) → x → x) → x) → (r → x) → x) (λ(str : String) → λ(x : *) → λ(PutStrLn : String → (∀(x : *) → (String → x) → x → x) → x) → λ(GetLine : (String → ∀(x : *) → (String → x) → x → x) → x) → λ(Return : r → x) → PutStrLn str (λ(x : *) → λ(Just : String → x) → λ(Nothing : x) → Nothing)) (λ(x : *) → λ(PutStrLn : String → (∀(x : *) → (String → x) → x → x) → x) → λ(GetLine : (String → ∀(x : *) → (String → x) → x → x) → x) → λ(Return : r → x) → GetLine (λ(va : String) → λ(x : *) → λ(Just : String → x) → λ(Nothing : x) → Just va)))"
