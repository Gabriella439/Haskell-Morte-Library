{-# LANGUAGE OverloadedStrings #-}

{-| A bare-bones calculus-of-constructions
-}

module Morte (
    -- * Types
    Var,
    Const(..),
    Expr(..),

    -- * Functions
    typeOf,
    normalize,
    pretty,

    -- * Utilities
    printValue,
    printType
    ) where

import Control.Monad.Trans.State (State, evalState, get, modify)
import Data.Monoid (mempty, (<>))
import Data.String (IsString(fromString))
import Data.Text.Lazy (Text, cons)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.IO as Text
import Data.Text.Lazy.Builder (Builder, toLazyText, fromLazyText)
import Data.Text.Lazy.Builder.Int (decimal)

-- TODO: Add a parser
-- TODO: Add support for '_' (unused variables)?

-- | Label for a bound variable
data Var = V Integer Text deriving (Eq, Show)

instance IsString Var
  where
    fromString str = V 0 (Text.pack str)

buildVar :: Var -> Builder
buildVar (V n txt) = fromLazyText txt <> if n == 0 then mempty else decimal n

type Context = [(Var, Expr)]

ppContext :: Context -> Builder
ppContext =
    fromLazyText . Text.unlines . map (toLazyText . ppKeyVal) . reverse
  where
    ppKeyVal (key, val) = buildVar key <> " : " <> buildExpr val

-- | Constants
data Const = Star | Box deriving (Eq, Show, Bounded, Enum)

buildConst :: Const -> Builder
buildConst c = case c of
    Star -> "*"
    Box  -> "BOX"

buildConsts :: Builder
buildConsts =
    fromLazyText (
        Text.intercalate ", " (
            map (toLazyText . buildConst) [minBound..maxBound] ) )

axiom :: Const -> Either Text Const
axiom Star = return Box
axiom Box  = Left "BOX has no type\n"

rule :: Const -> Const -> Either Text Const
rule Star Box  = return Box
rule Star Star = return Star
rule Box  Box  = return Box
rule Box  Star = return Star

-- | Syntax tree for expressions
data Expr
    = Const Const
    | Var Var
    | Lam Var Expr Expr
    | Pi  Var Expr Expr
    | App Expr Expr
    deriving (Show)

instance Eq Expr where
    eL0 == eR0 = evalState (go (normalize eL0) (normalize eR0)) []
      where
        go :: Expr -> Expr -> State [(Var, Var)] Bool
        go (Const cL) (Const cR) = return (cL == cR)
        go (Var nL) (Var nR) = do
            ctx <- get
            let n = case lookup nL ctx of
                    Nothing  -> nL
                    Just nR' -> nR'
            return (n == nR)
        go (Lam nL tL eL) (Lam nR tR eR) = do
            modify ((nL, nR):)
            b1 <- go tL tR
            b2 <- go eL eR
            return (b1 && b2)
        go (Pi nL tL eL) (Pi nR tR eR) = do
            modify ((nL, nR):)
            b1 <- go tL tR
            b2 <- go eL eR
            return (b1 && b2)
        go (App fL aL) (App fR aR) = do
            b1 <- go fL fR
            b2 <- go aL aR
            return (b1 && b2)
        go _ _ = return False

instance IsString Expr
  where
    fromString str = Var (fromString str)

buildExpr :: Expr -> Builder
buildExpr = go False False
  where
    go :: Bool -> Bool -> Expr -> Builder
    go parenBind parenApp e = case e of
        Const c    -> buildConst c
        Var v      -> buildVar v
        Lam v t e' ->
                (if parenBind then "(" else "")
            <>  "λ("
            <>  buildVar v
            <>  " : "
            <>  go False False t
            <>  ") → "
            <>  go False False e'
            <>  (if parenBind then ")" else "")
        Pi  v t e' ->
                (if parenBind then "(" else "")
            <>  (if used v e
                 then "∀(" <> buildVar v <> " : " <> go False False t <> ")"
                 else go True False t )
            <>  " → "
            <>  go False False e'
            <>  (if parenBind then ")" else "")
        App f x    ->
                (if parenApp then "(" else "")
            <>  go True False f <> " " <> go True True x
            <>  (if parenApp then ")" else "")

used :: Var -> Expr -> Bool
used v e = case e of
    Const _            -> False
    Var v' | v == v'   -> True
           | otherwise -> False
    Lam _ t e'         -> used v t || used v e'
    Pi  _ t e'         -> used v t || used v e'
    App f a            -> used v f || used v a

-- | Render an expression as pretty-printed `Text`
pretty :: Expr -> Text
pretty = toLazyText . buildExpr

toOdd :: Integer -> Integer
toOdd n = 2 * n + 1

toEven :: Integer -> Integer
toEven n = 2 * n

renumber :: (Integer -> Integer) -> Expr -> Expr
renumber k = go 
  where
    go e = case e of
        Lam v@(V n l) t e' ->
            let v' = V (k n) l in Lam v' t (subst v (Var v') e')
        Pi  v@(V n l) t e' ->
            let v' = V (k n) l in Pi  v' t (subst v (Var v') e')
        App f a            -> App (go f) (go a)
        _                  -> e

subst :: Var -> Expr -> Expr -> Expr
subst n0 eL eR = go eR'
  where
    go e = case e of
        Lam n t e' -> if n == n0 then e else Lam n (go t) (go e')
        Pi  n t e' -> if n == n0 then e else Pi  n (go t) (go e')
        App f a    -> App (go f) (go a)
        Var n      -> if (n == n0) then eL' else e
        _          -> e

    eL' = renumber toOdd  eL
    eR' = renumber toEven eR

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
        e' <- fmap whnf (typeOf_ ctx f)
        (x, _A, _B) <- case e' of
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
    Lam x t e' -> case normalize e' of
        App f a -> case normalize a of
            Var x' | x == x'   -> normalize f
                   | otherwise -> l
            _                  -> l
        _                      -> l
      where
        e'' = normalize e'
        l   = Lam x (normalize t) e''
    Pi  x t e' -> Pi  x (normalize t) (normalize e')
    App f _C   -> case normalize f of
        Lam x _A _B -> normalize (subst x _C _B)
        f'          -> App f' (normalize _C)
    _       -> e

-- | Pretty-print an expression
printValue :: Expr -> IO ()
printValue = Text.putStrLn . pretty

{-| Pretty print an expression's type, or output an error message if type
    checking fails
-}
printType :: Expr -> IO ()
printType expr = case typeOf expr of
    Left err -> Text.putStr err
    Right t  -> Text.putStrLn (pretty t)
