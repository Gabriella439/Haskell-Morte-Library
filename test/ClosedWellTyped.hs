{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module ClosedWellTyped (
    ClosedWellTyped(..)
    ) where

import Control.Applicative hiding (Const)
import Control.Monad (guard)
import Data.Text.Lazy (Text)
import Control.Monad.State.Lazy (MonadState, StateT)
import Control.Monad.Trans.Class (lift)
import Morte.Core
import Test.QuickCheck (Arbitrary, Gen)

import qualified Control.Monad.State.Lazy as State
import qualified Data.Text.Lazy           as Text
import qualified Test.QuickCheck          as QuickCheck

newtype ClosedWellTyped = ClosedWellTyped { unClosedWellTyped :: Expr X }
    deriving Show

data Env = Env
    { bindings :: [(Var, Expr X)]
    , uniques  :: [Text]
    }

newtype M a = M { unM :: StateT Env Gen a }
    deriving (Functor, Applicative, Monad, MonadState Env)

liftGen :: Gen a -> M a
liftGen m = M (lift m)

evalM :: M a -> Env -> Gen a
evalM m = State.evalStateT (unM m)

instance Arbitrary ClosedWellTyped
  where
    arbitrary = QuickCheck.sized rndExpr

rndExpr :: Int -> Gen ClosedWellTyped
rndExpr n = fmap ClosedWellTyped (evalM genClosed (initEnv n))

initEnv :: Int -> Env
initEnv n = Env
    { bindings = []
    , uniques  = map (Text.pack . show) [1..n]
    }

extend :: Var -> Expr X -> M ()
extend x t = State.modify (\env -> env { bindings = (x, t) : bindings env })

select :: [(Int, M (Expr X, Expr X), Env -> Bool)] -> M (Expr X, Expr X)
select wgps = do
    env <- State.get
    m <- liftGen (QuickCheck.frequency (do
        (weight, generator, predicate) <- wgps
        guard (predicate env)
        return (weight, return generator) ))
    m

scope :: M a -> M a
scope f = do
    env <- State.get
    liftGen (evalM f env)

buildPi :: Text -> Expr X -> Expr X -> Expr X -> (Expr X, Expr X)
buildPi x _M _N _Nt = (Pi x _M _N, _Nt)

buildLambda :: Text -> Expr X -> Expr X -> Expr X -> (Expr X, Expr X)
buildLambda x _M _N _Nt = (Lam x _M _N, Pi x _M _Nt)

matching :: Eq b => b -> [(a, b)] -> Bool
matching t = any ((t ==) . snd)

moreThan :: Int -> [a] -> Bool
moreThan n = not . null . drop n

piFilter :: Expr X -> Expr X -> Bool
piFilter t (Pi _ _A _) = _A == t
piFilter _  _          = False

-- TODO: Also generate `Pi` here?
genClosed :: M (Expr X)
genClosed =
    fmap fst
        (select
            [ (20, genContext, \_ -> True          )
            , (50, genLambda , moreThan 0 . uniques)
            , (30, genApp    , moreThan 1 . uniques)
            ] )

-- TODO: Also generate `Const` here?
genObj :: M (Expr X, Expr X)
genObj =
    select
        [ (5,  genObjPi , moreThan 0 . uniques )
        , (50, genLambda, moreThan 0 . uniques )
        , (25, genVar   , moreThan 0 . bindings)
        , (20, genApp   ,
            \e  ->  (null       (bindings e) && moreThan 1 (uniques e))
                ||  (moreThan 0 (bindings e) && moreThan 0 (uniques e)) )
        ]

genContext :: M (Expr X, Expr X)
genContext =
    select
        [ (15, return (Const Star,Const Box), \_ -> True                      )
        , (20, genVarOf (Const Star)        , matching (Const Star) . bindings)
        , (15, genPi                        , moreThan 0            . uniques )
        ]

genVar :: M (Expr X, Expr X)
genVar = genVarWith (\_ -> True)

genVarOf :: Expr X -> M (Expr X, Expr X)
genVarOf t = genVarWith (t ==)

genPiVarOf :: Expr X -> M (Expr X, Expr X)
genPiVarOf t = genVarWith (piFilter t)

genVarWith :: (Expr X -> Bool) -> M (Expr X, Expr X)
genVarWith f = do
    bEnv <- State.gets bindings
    liftGen (QuickCheck.elements (do
        (x, y) <- bEnv
        guard (f y)
        return (Var x, y) ))

genPi :: M (Expr X, Expr X)
genPi = genAbsWith (scope genContext) genContext buildPi

genObjPi :: M (Expr X, Expr X)
genObjPi = genAbsWith (scope genContext) genBody buildPi
  where
    genBody =
        select
            [ (20, genVarOf (Const Star), matching (Const Star) . bindings)
            , (15, genObjPi             , moreThan 0            . uniques)
            ]

genLambda :: M (Expr X, Expr X)
genLambda = genAbsWith (scope genContext) genObj buildLambda

genLambdaOf :: Expr X -> M (Expr X, Expr X)
genLambdaOf _M = genAbsWith (return (_M, Const Star)) genObj buildLambda

genAbsWith
    :: M (Expr X, Expr X)
    -> M (Expr X, Expr X)
    -> (Text -> Expr X -> Expr X -> Expr X -> (Expr X, Expr X))
    -> M (Expr X, Expr X)
genAbsWith gT gB build = do
    st <- State.get
    let (x:xs) = uniques st
    State.put (st { uniques = xs })
    (_M, _) <- gT
    extend (V x 0) _M
    (_N, _Nt) <- gB
    return (build x _M _N _Nt)

genApp :: M (Expr X, Expr X)
genApp = do
    (_N, _A       ) <- scope genObj
    (f , Pi x _ _B) <- do
        scope
            (select
                [ (40, genLambdaOf _A, moreThan 0              . uniques)
                , (20, genPiVarOf  _A, any (piFilter _A . snd) . bindings)
                ] )
    return (App f _N, subst x 0 _N _B)
