module Main (
    main
  ) where

import Test.Tasty
import Test.Tasty.QuickCheck as QC

import Morte.Core
import ClosedWellTyped

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Properties" [
      QC.testProperty "normalize . normalize == normalize" normalizeIdempotent 
    , QC.testProperty "Well typed after normalization"     wellTypedAfterNormalize
    ]

wellTypedAfterNormalize :: ClosedWellTyped -> Bool
wellTypedAfterNormalize (ClosedWellTyped expr) = 
        not (isRight $ typeOf expr) || (isRight $ typeOf $ normalize expr)

normalizeIdempotent :: ClosedWellTyped -> Bool
normalizeIdempotent (ClosedWellTyped expr) = normalize nExpr == nExpr
    where nExpr = normalize expr

isRight :: Either a b -> Bool
isRight (Left  _) = False
isRight (Right _) = True
