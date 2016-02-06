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
import Prelude hiding (pi)
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
rndExpr n = fmap (ClosedWellTyped . fst) (evalM closed (initEnv n))

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
    m   <- liftGen (QuickCheck.frequency (do
        (weight, generator, predicate) <- wgps
        guard (predicate env)
        return (weight, return generator) ))
    m

scope :: M a -> M a
scope f = do
    env <- State.get
    liftGen (evalM f env)

matching :: Eq b => b -> [(a, b)] -> Bool
matching t = any ((t ==) . snd)

moreThan :: Int -> [a] -> Bool
moreThan n = not . null . drop n

piFilter :: Expr X -> Expr X -> Bool
piFilter t (Pi _ _A _) = _A == t
piFilter _  _          = False

closed :: M (Expr X, Expr X)
closed =
    select
        [ (20, typeOrKind                       , \_ -> True          )
        , (50, lam (scope typeOrKind) termOrType, moreThan 0 . uniques)
        , (30, app                              , moreThan 1 . uniques)
        ]

termOrType :: M (Expr X, Expr X)
termOrType =
    select
        [ ( 5, type_                            , moreThan 0 . uniques )
        , (50, lam (scope typeOrKind) termOrType, moreThan 0 . uniques )
        , (25, var                              , moreThan 0 . bindings)
        , (20, app                              ,
            \e  ->  (null       (bindings e) && moreThan 1 (uniques e))
                ||  (moreThan 0 (bindings e) && moreThan 0 (uniques e)) )
        ]

typeOrKind :: M (Expr X, Expr X)
typeOrKind =
    select
        [ (15, return (Const Star,Const Box)   , \_ -> True                      )
        , (20, varWith (== Const Star)         , matching (Const Star) . bindings)
        , (15, pi (scope typeOrKind) typeOrKind, moreThan 0            . uniques )
        ]

varWith :: (Expr X -> Bool) -> M (Expr X, Expr X)
varWith f = do
    bEnv <- State.gets bindings
    liftGen (QuickCheck.elements (do
        (x, y) <- bEnv
        guard (f y)
        return (Var x, y) ))

var :: M (Expr X, Expr X)
var = varWith (\_ -> True)

type_ :: M (Expr X, Expr X)
type_ =
    select
        [ (20, varWith (== Const Star)     , matching (Const Star) . bindings)
        , (15, pi (scope typeOrKind) type_ , moreThan 0            . uniques )
        ]

fresh :: M Text
fresh = do
    env <- State.get
    let x:xs = uniques env
    State.put (env { uniques = xs })
    return x

lam :: M (Expr X, Expr X)
    -> M (Expr X, Expr X)
    -> M (Expr X, Expr X)
lam _AGen bGen = do
    x <- fresh
    (_A, _) <- _AGen
    extend (V x 0) _A
    (b, bType) <- bGen
    return (Lam x _A b, Pi x _A bType)

pi  :: M (Expr X, Expr X)
    -> M (Expr X, Expr X)
    -> M (Expr X, Expr X)
pi _AGen _BGen = do
    x <- fresh
    (_A, _) <- _AGen
    extend (V x 0) _A
    (_B, _BType) <- _BGen
    return (Pi x _A _B, _BType)

app :: M (Expr X, Expr X)
app = do
    (_N, _A       ) <- scope termOrType
    let genA = return (_A, Const Star)
    (f , Pi x _ _B) <- do
        scope
            (select
                [ (40, lam genA termOrType  , moreThan 0              . uniques )
                , (20, varWith (piFilter _A), any (piFilter _A . snd) . bindings)
                ] )
    return (App f _N, subst x 0 _N _B)
