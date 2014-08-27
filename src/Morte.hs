{-# LANGUAGE OverloadedStrings #-}

{-| A bare-bones calculus-of-constructions
-}

module Morte (
    -- * Types
    Const(..),
    Expr(..),

    -- * Functions
    typeOf,
    normalize,
    pretty
    ) where

import Control.Applicative (pure, (*>), (<|>))
import Control.Monad.Trans.State (evalState, get, put)
import qualified Data.IntMap.Strict as IntMap
import Data.Monoid (mempty, (<>))
import Data.Text.Lazy (Text, intercalate, unpack)
import qualified Data.Text.Lazy as Text
import Data.Text.Lazy.Builder (Builder, toLazyText, fromLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import Prelude hiding (const, succ, id)

-- TODO: Allow type-checking with a context
-- TODO: Add free variables
-- TODO: Add a parser

type Context = IntMap.IntMap Expr

ppContext :: Context -> Builder
ppContext =
    fromLazyText . Text.unlines . map (toLazyText . ppKeyVal) . IntMap.assocs
  where
    ppKeyVal (key, val) = "x" <> decimal key <> ": " <> buildExpr val

-- | Constants
data Const = Star | Box deriving (Eq, Show, Bounded, Enum)

buildConst :: Const -> Builder
buildConst c = case c of
    Star -> "*"
    Box  -> "BOX"

buildConsts :: Builder
buildConsts =
    fromLazyText (
        intercalate ", " (map (toLazyText . buildConst) [minBound..maxBound]) )

axiom :: Const -> Either Text Const
axiom Star = return Box
axiom Box  = Left "BOX has no type\n"

rule :: Const -> Const -> Either Text Const
rule Star Box  = return Box
rule Star Star = return Star
rule Box  Box  = return Box
rule Box  Star = return Star

-- | Higher-order abstract syntax tree for expressions
data Expr
    = Const Const
    | Var Int
    | Lam Expr (Expr -> Expr)
    | Pi Expr (Expr -> Expr)
    | App Expr Expr

instance Eq Expr where
    e1 == e2 = quote (normalize e1) == quote (normalize e2)

instance Show Expr where
    show = unpack . pretty

buildExpr :: Expr -> Builder
buildExpr = buildQuoted . quote

data Quoted
    = Const' Const
    | Var' Int
    | Lam' Int Quoted Quoted
    | Pi'  Int Quoted Quoted
    | App' Quoted Quoted
    deriving (Eq, Show)

buildQuoted :: Quoted -> Builder
buildQuoted = go False False
  where
    go :: Bool -> Bool -> Quoted -> Builder
    go parenBind parenApp e = case e of
        Const' c    -> buildConst c
        Var' n      -> "x" <> decimal n
        Lam' n t e' ->
                (if parenBind then "(" else "")
            <>  "λ(x"
            <>  decimal n
            <>  " : "
            <>  go False False t
            <>  ") → "
            <>  go False False e'
            <>  (if parenBind then ")" else "")
        Pi' n t e'  ->
                (if parenBind then "(" else "")
            <>  (if used n e
                 then "∀(x" <> decimal n <> " : " <> go False False t <> ")"
                 else go True False t )
            <>  " → "
            <>  go False False e'
            <>  (if parenBind then ")" else "")
        App' f x    ->
                (if parenApp then "(" else "")
            <>  go True False f <> " " <> go True True x
            <>  (if parenApp then ")" else "")

used :: Int -> Quoted -> Bool
used n e = case e of
    Const' _            -> False
    Var' n' | n == n'   -> True
            | otherwise -> False
    Lam' _ t e'         -> used n t || used n e'
    Pi'  _ t e'         -> used n t || used n e'
    App' f a            -> used n f || used n a

quote :: Expr -> Quoted
quote e0 = evalState (go e0) 1
  where
    go e = case e of
        Const c -> return (Const' c)
        Var   n -> return (Var' n)
        Lam t f -> do
            n <- get
            put $! n + 1
            t' <- go t
            e' <- go (f (Var n))
            return (Lam' n t' e')
        Pi  t f -> do
            n <- get
            put $! n + 1
            t' <- go t
            e' <- go (f (Var n))
            return (Pi' n t' e')
        App f a -> do
            f' <- go f
            a' <- go a
            return (App' f' a')

-- | Pretty-print an expression as lazy `Text`
pretty :: Expr -> Text
pretty = toLazyText . buildExpr

subst :: Int -> Expr -> Expr -> Expr
subst n0 e0 = go
  where
    go e = case e of
        Lam t k  -> Lam (go t) (go . k)
        Pi  t k  -> Pi  (go t) (go . k)
        App f a  -> App (go f) (go a)
        Var n    -> case e0 of
            Var m -> Var (if n == n0 then m else n)
            _ | n == n0   -> e0
              | otherwise -> e
        _        -> e

typeOf_ :: Context -> Expr -> Either Text Expr
typeOf_ ctx e0 = case e0 of
    Const c  -> fmap Const (axiom c)
    Var x    -> case IntMap.lookup x ctx of
        Nothing -> Left (toLazyText (
                header
            <>  "Error: Unbound variable\n" ) )
        Just a  -> return a
    Lam _A k -> do
        let x = case IntMap.keys ctx of
                [] -> 0
                es -> minimum es - 1
        _B <- typeOf_ (IntMap.insert x _A ctx) (k (Var x))
        let e = Pi _A (\e' -> subst x e' _B)
        _t <- typeOf_ ctx e
        return e
    Pi  _A k -> do
        eS <- fmap whnf (typeOf_ ctx _A)
        s  <- case eS of
            Const s -> return s
            _       -> Left (toLazyText (
                    header
                <>  "Error: The variable bound by the ∀ has an invalid type\n"
                <>  "\n"
                <>  "Value: " <> buildExpr _A <> "\n"
                <>  "Actual type: " <> buildExpr eS <> "\n"
                <>  "Valid types: " <> buildConsts  <> "\n" ) )
        let x = case IntMap.keys ctx of
                [] -> 0
                es -> minimum es - 1
        eT <- fmap whnf (typeOf_ (IntMap.insert x _A ctx) (k (Var x)))
        t  <- case eT of
            Const t -> return t
            _       -> Left (toLazyText (
                    header
                <>  "Error: The value returned by the ∀ has an invalid type\n"
                <>  "\n"
                <>  "Actual type: " <> buildExpr eT <> "\n"
                <>  "Valid types: " <> buildConsts  <> "\n" ) )
        fmap Const (rule s t)
    App f a  -> do
        e       <- fmap whnf (typeOf_ ctx f)
        (_A, k) <- case e of
            Pi _A k -> return (_A, k)
            _          -> Left (toLazyText (
                    header
                <>  "Error: Only functions may be applied to values\n" ) )
        _A' <- typeOf_ ctx a
        let nf_A  = quote (normalize _A )
            nf_A' = quote (normalize _A')
        if nf_A == nf_A'
            then return (k a)
            else Left (toLazyText (
                    header
                <>  "Error: Function applied to argument of the wrong type\n"
                <>  "\n"
                <>  "Expected type: " <> buildQuoted nf_A  <> "\n"
                <>  "Argument type: " <> buildQuoted nf_A' <> "\n" ) )
  where
    ppCtx = ppContext ctx
    header =
            (if Text.null (toLazyText ppCtx)
             then mempty
             else "Context:\n" <> ppContext ctx <> "\n")
        <>  "Expression: " <> buildExpr e0 <> "\n"
        <>  "\n"

-- | Type-check an expression and return the expression's type
typeOf :: Expr -> Either Text Expr
typeOf = typeOf_ IntMap.empty

whnf :: Expr -> Expr
whnf e = case e of
    App f _C -> case whnf f of
        Lam _ k -> whnf (k _C)
        _       -> e
    _    -> e

-- | Reduce an expression to normal form
normalize :: Expr -> Expr
normalize e = case e of
    Lam t k  -> Lam (normalize t) (normalize . k)
    Pi  t k  -> Pi  (normalize t) (normalize . k)
    App f _C -> case normalize f of
        Lam _ k -> normalize (k _C)
        _       -> e
    _       -> e
