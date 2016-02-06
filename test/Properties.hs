module Main (
    main
  ) where

import Test.Tasty
import Test.Tasty.QuickCheck as QuickCheck

import Morte.Core
import ClosedWellTyped

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Properties"
    [ QuickCheck.testProperty "Normalization is idempotent"
        normalizeIdempotent 
    , QuickCheck.testProperty "Normalization preserves type safety"
        wellTypedAfterNormalize
    ]

wellTypedAfterNormalize :: ClosedWellTyped -> Property
wellTypedAfterNormalize (ClosedWellTyped expr) = 
    isRight (typeOf expr) ==> isRight (typeOf (normalize expr))

normalizeIdempotent :: ClosedWellTyped -> Bool
normalizeIdempotent (ClosedWellTyped expr) = normalize nExpr == nExpr
  where
    nExpr = normalize expr

isRight :: Either a b -> Bool
isRight (Left  _) = False
isRight (Right _) = True
