module Main (
    main
  ) where

import ClosedWellTyped (ClosedWellTyped(..))
import Morte.Core
import Test.Tasty (TestTree)

import qualified Test.Tasty            as Tasty
import qualified Test.Tasty.QuickCheck as QuickCheck

main :: IO ()
main = Tasty.defaultMain tests

tests :: TestTree
tests = Tasty.testGroup "Properties"
    [ QuickCheck.testProperty "Normalization is idempotent"
        normalizationIsIdempotent 
    , QuickCheck.testProperty "Normalization preserves type safety"
        normalizationPreservesTypeSafety
    ]

typeChecks :: Expr X -> Bool
typeChecks expr = case typeOf expr of
    Right _ -> True
    Left  _ -> False

-- Carefully note that `ClosedWellTyped` generates well-typed expressions, so
-- this is really testing that `typeChecks expr ==> typeChecks (normalize expr)`
normalizationPreservesTypeSafety :: ClosedWellTyped -> Bool
normalizationPreservesTypeSafety (ClosedWellTyped expr) =
    typeChecks (normalize expr)

-- Carefully note that `(==)` also normalizes both sides before checking for
-- α-equality, so this is really testing that `normalize (normalize expr)` and
-- `normalize expr` are α-equivalent.
normalizationIsIdempotent :: ClosedWellTyped -> Bool
normalizationIsIdempotent (ClosedWellTyped expr) = normalize expr == expr
