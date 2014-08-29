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
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State (evalStateT, get, put)
import Data.Monoid (mempty, (<>))
import Data.Text.Lazy (Text, intercalate, unpack)
import qualified Data.Text.Lazy as Text
import Data.Text.Lazy.Builder (Builder, toLazyText, fromLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import Prelude hiding (const, succ, id)

-- TODO: Add a parser
-- TODO: Decide on lazy versus strict Text
-- TODO: Add support for '_' (unused variables)
-- TODO: Implement `quote` more elegantly

type Var = Text

type Context = [(Var, Expr)]

ppContext :: Context -> Builder
ppContext =
    fromLazyText . Text.unlines . map (toLazyText . ppKeyVal)
  where
    ppKeyVal (key, val) = fromLazyText key <> " : " <> buildExpr val

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
    | Var Var
    | Lam Var Expr Expr
    | Pi  Var Expr Expr
    | App Expr Expr

instance Eq Expr where
    e1 == e2 = case cmp of
        Nothing -> False
        Just b  -> b
      where
        cmp = do
            q1 <- quote (normalize e1)
            q2 <- quote (normalize e2)
            return (q1 == q2)

instance Show Expr where
    show = unpack . pretty

data Quoted
    = Const' Const
    | Var' Int
    | Lam' Int Quoted Quoted
    | Pi'  Int Quoted Quoted
    | App' Quoted Quoted
    deriving (Eq, Show)

buildExpr :: Expr -> Builder
buildExpr = go False False
  where
    go :: Bool -> Bool -> Expr -> Builder
    go parenBind parenApp e = case e of
        Const c    -> buildConst c
        Var n      -> fromLazyText n
        Lam n t e' ->
                (if parenBind then "(" else "")
            <>  "λ("
            <>  fromLazyText n
            <>  " : "
            <>  go False False t
            <>  ") → "
            <>  go False False e'
            <>  (if parenBind then ")" else "")
        Pi n t e'  ->
                (if parenBind then "(" else "")
            <>  (if used n e
                 then "∀(" <> fromLazyText n <> " : " <> go False False t <> ")"
                 else go True False t )
            <>  " → "
            <>  go False False e'
            <>  (if parenBind then ")" else "")
        App f x    ->
                (if parenApp then "(" else "")
            <>  go True False f <> " " <> go True True x
            <>  (if parenApp then ")" else "")

used :: Text -> Expr -> Bool
used n e = case e of
    Const _            -> False
    Var n' | n == n'   -> True
           | otherwise -> False
    Lam _ t e'         -> used n t || used n e'
    Pi  _ t e'         -> used n t || used n e'
    App f a            -> used n f || used n a

quote :: Expr -> Maybe Quoted
quote e0 = evalStateT (go e0) (0, [])
  where
    go e = case e of
        Const c    -> return (Const' c)
        Var n      -> do
            (_, ps) <- get
            k       <- lift (lookup n ps)
            return (Var' k)
        Lam n t e' -> do
            (i, ps) <- get
            put (i + 1, (n, i):ps)
            t'  <- go t
            e'' <- go e'
            return (Lam' i t' e'')
        Pi  n t e' -> do
            (i, ps) <- get
            put (i + 1, (n, i):ps)
            t'  <- go t
            e'' <- go e'
            return (Pi' i t' e'')
        App f a    -> do
            f' <- go f
            a' <- go a
            return (App' f' a')

-- | Pretty-print an expression as lazy `Text`
pretty :: Expr -> Text
pretty = toLazyText . buildExpr

subst :: Text -> Expr -> Expr -> Expr
subst n0 e0 = go
  where
    go e = case e of
        Lam n t e' -> if n == n0 then e else Lam n (go t) (go e')
        Pi  n t e' -> if n == n0 then e else Pi  n (go t) (go e')
        App f a    -> App (go f) (go a)
        Var n      -> if (n == n0) then e0 else e
        _          -> e

typeOf_ :: Context -> Expr -> Either Text Expr
typeOf_ ctx e = case e of
    Const c  -> fmap Const (axiom c)
    Var x    -> case lookup x ctx of
        Nothing -> Left (toLazyText (
                header
            <>  "Error: Unbound variable\n" ) )
        Just a  -> return a
    Lam x _A b -> do
        _B <- typeOf_ ((x, _A):ctx) b
        let p = Pi x _A _B
        _t <- typeOf_ ctx p
        return p
    Pi  x _A _B -> do
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
        eT <- fmap whnf (typeOf_ ((x, _A):ctx) _B)
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
        (x, _A, _B) <- case e of
            Pi x _A _B -> return (x, _A, _B)
            _          -> Left (toLazyText (
                    header
                <>  "Error: Only functions may be applied to values\n" ) )
        _A' <- typeOf_ ctx a
        let nf_A  = normalize _A 
            nf_A' = normalize _A'
        if nf_A == nf_A'
            then return (subst x a _B)
            else Left (toLazyText (
                    header
                <>  "Error: Function applied to argument of the wrong type\n"
                <>  "\n"
                <>  "Expected type: " <> buildExpr nf_A  <> "\n"
                <>  "Argument type: " <> buildExpr nf_A' <> "\n" ) )
  where
    ppCtx = ppContext ctx
    header =
            (if Text.null (toLazyText ppCtx)
             then mempty
             else "Context:\n" <> ppContext ctx <> "\n")
        <>  "Expression: " <> buildExpr e <> "\n"
        <>  "\n"

-- | Type-check an expression and return the expression's type
typeOf :: Expr -> Either Text Expr
typeOf = typeOf_ []

whnf :: Expr -> Expr
whnf e = case e of
    App f _C -> case whnf f of
        Lam x _A _B -> whnf (subst x _C _B)
        _           -> e
    _    -> e

-- | Reduce an expression to normal form
normalize :: Expr -> Expr
normalize e = case e of
    Lam x t e' -> Lam x (normalize t) (normalize e')
    Pi  x t e' -> Pi  x (normalize t) (normalize e')
    App f _C   -> case normalize f of
        Lam x _A _B -> normalize (subst x _C _B)
        _           -> e
    _       -> e
