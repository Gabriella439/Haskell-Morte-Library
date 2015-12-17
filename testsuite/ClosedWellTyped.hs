module ClosedWellTyped (
    ClosedWellTyped(..)
    ) where

import Control.Applicative as A ((<$>))
import Control.Monad.State.Lazy
import Data.Text.Lazy (Text, pack)
import Test.QuickCheck

import Morte.Core


newtype ClosedWellTyped = ClosedWellTyped { unClosedWellTyped :: Expr X }
    deriving Show

data Env a = Env {
      bindings :: [(Var, Expr a)]
    , uniques  :: [Text]
    }

type GenExpr e a   = StateT (Env e) Gen a
type GenExprPair e = StateT (Env e) Gen (Expr e,Expr e)

instance Arbitrary ClosedWellTyped where
    arbitrary = sized rndExpr


rndExpr :: Int -> Gen ClosedWellTyped
rndExpr n = ClosedWellTyped <$> evalStateT genExpr (initEnv n)

initEnv :: Int -> Env a
initEnv n = Env [] $ map (pack . show) [1..n]

extend :: Var -> Expr e -> GenExpr e ()
extend x t = modify (\env -> env { bindings = (x,t) : bindings env })

select :: [(Int,GenExprPair e,Env e -> Bool)] -> GenExprPair e
select wgps = do
    env <- get
    join $ lift $ frequency $ foldr (\(w,g,prcd) wgs -> if prcd env 
                                                        then (w,return g) : wgs
                                                        else wgs) [] wgps

scope :: GenExpr e a -> GenExpr e a
scope f = get >>= lift . evalStateT f

substUniq :: Text -> Expr a -> Expr a -> Expr a
substUniq x e' e = case e of
    Lam x' _A  b  -> Lam x' (substUniq x e' _A) (substUniq x e' b)
    Pi  x' _A _B  -> Pi  x' (substUniq x e' _A) (substUniq x e' _B)
    App f a       -> App (substUniq x e' f) (substUniq x e' a)
    Var (V x' _) -> if x == x' then e' else e
    Const k       -> Const k
    Embed p       -> Embed p

buildPi :: Text -> Expr e -> Expr e -> Expr e -> (Expr e,Expr e)
buildPi x _M _N _Nt = (Pi x _M _N, _Nt)

buildLambda :: Text -> Expr e -> Expr e -> Expr e -> (Expr e, Expr e)
buildLambda x _M _N _Nt = (Lam x _M _N, Pi x _M _Nt)

uniquesAvailable :: Env e -> Bool
uniquesAvailable = not . null . uniques

bindingOfAvailable :: Eq e => Expr e -> Env e -> Bool
bindingOfAvailable t = any ((t ==) . snd) . bindings

bindingsAvailable :: Env e -> Bool
bindingsAvailable = not . null . bindings

piFilter :: Eq e => Expr e -> Expr e -> Bool
piFilter t (Pi _ _A _) = _A == t
piFilter _ _           = False


genExpr :: Eq e => GenExpr e (Expr e)
genExpr = fst <$> select [ (20, genContext, const True)
                         , (50, genLambda , uniquesAvailable)
                         , (30, genApp    , \e -> length (uniques e) > 1)
                         ]

genObj :: Eq e => GenExprPair e
genObj = select [ (5,  genObjPi , uniquesAvailable)
                , (50, genLambda, uniquesAvailable)
                , (25, genVar   , bindingsAvailable)
                , (20, genApp   , \e -> (null (bindings e) && length (uniques e) > 1) 
                                     || (bindingsAvailable e && uniquesAvailable e)
                  )
                ]

genContext :: Eq e => GenExprPair e
genContext = select [ (15, return (Const Star,Const Box), const True)
                    , (20, genVarOf (Const Star)        , bindingOfAvailable (Const Star))
                    , (15, genPi                        , uniquesAvailable)
                    ]


genVar :: Eq e => GenExprPair e
genVar = genVarWith (const True)

genVarOf :: Eq e => Expr e -> GenExprPair e
genVarOf t = genVarWith (t ==)

genPiVarOf :: Eq e => Expr e -> GenExprPair e
genPiVarOf t = genVarWith (piFilter t)

genVarWith :: Eq e => (Expr e -> Bool) -> GenExprPair e
genVarWith f = do
    bEnv' <- gets bindings
    let bEnv = filter (f . snd) bEnv'
    lift $ (\x -> (Var $ fst x, snd x)) A.<$> elements bEnv


genPi :: Eq e => GenExprPair e
genPi = genAbsWith (scope genContext) genContext buildPi

genObjPi :: Eq e => GenExprPair e
genObjPi = genAbsWith (scope genContext) genBody buildPi
    where genBody = select [ (20, genVarOf (Const Star), bindingOfAvailable (Const Star))
                           , (15, genObjPi             , uniquesAvailable)
                           ]


genLambda :: Eq e => GenExprPair e
genLambda = genAbsWith (scope genContext) genObj buildLambda

genLambdaOf :: Eq e => Expr e -> GenExprPair e
genLambdaOf _M = genAbsWith (return (_M,Const Star)) genObj buildLambda


genAbsWith :: GenExprPair e
           -> GenExprPair e
           -> (Text -> Expr e -> Expr e -> Expr e -> (Expr e,Expr e))
           -> GenExprPair e
genAbsWith gT gB build = do
    st <- get
    let (x:xs) = uniques st
    put $ st { uniques = xs }
    (_M,_) <- gT
    extend (V x 0) _M
    (_N,_Nt) <- gB
    return $ build x _M _N _Nt

genApp :: Eq e => GenExprPair e
genApp = do
    (_N, _A)      <- scope genObj
    (f,Pi x _ _B) <- scope $ select [ (40, genLambdaOf _A, uniquesAvailable)
                                    , (20, genPiVarOf  _A, any (piFilter _A . snd) . bindings)
                                    ]
    return (App f _N, substUniq x _N _B)
