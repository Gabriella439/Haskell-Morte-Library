{-# LANGUAGE OverloadedStrings #-}

{-| This module contains the core calculus for the Morte language.  This language
    is a minimalist implementation of the calculus of constructions, which is in
    turn a specific kind of pure type system.  If you are new to pure type
    systems you may wish to read:
    <http://research.microsoft.com/en-us/um/people/simonpj/papers/henk.ps.gz Henk: a typed intermediate language>.

    Morte emphasizes one important feature:

    * All expressions are strongly normalizable (using `normalize`)
    * Expressions can be tested for equality (using `==`)


    These two features give rise to the following emergent properties:

    * Programs that are equal (via equational reasoning) normalize to identical
      expressions (modulo alpha conversion), generate identical machine code, and
      yield identical performance
    * When you `normalize` your program, you only pay for abstraction at
      compile-time, not run-time


    This comes at a price: Morte forbids recursion.  Instead, you must translate
    all recursion to F-algebras and translate all corecursion to F-coalgebras.
-}

module Morte (
    -- * Types
    Var(..),
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
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.String (IsString(fromString))
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.IO as Text
import Data.Text.Lazy.Builder (Builder, toLazyText, fromLazyText)
import Data.Text.Lazy.Builder.Int (decimal)

-- TODO: Add a parser
-- TODO: Provide a structured error type
-- TODO: Add support for '_' (unused variables)?

{-| Label for a bound variable

    The `Text` field is the variable's name.

    The `Int` field disambiguates variables with the same name.  Zero is a good
    default.  Non-zero values will appear as a numeric suffix when
    pretty-printing the `Var`.
-}
data Var = V Text Int deriving (Eq, Show)

instance IsString Var
  where
    fromString str = V (Text.pack str) 0

buildVar :: Var -> Builder
buildVar (V txt n) = fromLazyText txt <> if n == 0 then mempty else decimal n

type Context = [(Var, Expr)]

ppContext :: Context -> Builder
ppContext =
    fromLazyText . Text.unlines . map (toLazyText . ppKeyVal) . reverse
  where
    ppKeyVal (key, val) = buildVar key <> " : " <> buildExpr val

{-| Constants for the calculus of constructions

    The only axiom is:

> ⊦ * : □

    ... and all four rule pairs are valid:

> ⊦ * ↝ * : *
> ⊦ □ ↝ * : *
> ⊦ * ↝ □ : □
> ⊦ □ ↝ □ : □

-}
data Const = Star | Box deriving (Eq, Show, Bounded, Enum)

buildConst :: Const -> Builder
buildConst c = case c of
    Star -> "*"
    Box  -> "□"

buildConsts :: Builder
buildConsts =
    fromLazyText (
        Text.intercalate ", " (
            map (toLazyText . buildConst) [minBound..maxBound] ) )

axiom :: Const -> Either Text Const
axiom Star = return Box
axiom Box  = Left "□ has no type\n"

rule :: Const -> Const -> Either Text Const
rule Star Box  = return Box
rule Star Star = return Star
rule Box  Box  = return Box
rule Box  Star = return Star

-- | Syntax tree for expressions
data Expr
    -- | > Const c        ~  c
    = Const Const
    -- | > Var (V x 0)    ~  x
    --   > Var (V x n)    ~  xn
    | Var Var
    -- | > Lam x A b      ~  λ(x : A) → b
    | Lam Var Expr Expr
    -- | > Pi x      A B  ~  ∀(x : A) → B
    --   > Pi unused A B  ~        A  → B
    | Pi  Var Expr Expr
    -- | > App f a        ~  f a
    | App Expr Expr
    deriving (Show)

    -- @Var (V x 0)  ~  x             |  Var (V x n)    ~  xn@
instance Eq Expr where
    eL0 == eR0 = evalState (go (normalize eL0) (normalize eR0)) []
      where
        go :: Expr -> Expr -> State [(Var, Var)] Bool
        go (Const cL) (Const cR) = return (cL == cR)
        go (Var xL) (Var xR) = do
            ctx <- get
            let x = case lookup xL ctx of
                    Nothing  -> xL
                    Just xR' -> xR'
            return (x == xR)
        go (Lam xL tL bL) (Lam xR tR bR) = do
            modify ((xL, xR):)
            eq1 <- go tL tR
            eq2 <- go bL bR
            return (eq1 && eq2)
        go (Pi xL tL bL) (Pi xR tR bR) = do
            modify ((xL, xR):)
            eq1 <- go tL tR
            eq2 <- go bL bR
            return (eq1 && eq2)
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
        Var x      -> buildVar x
        Lam x _A b ->
                (if parenBind then "(" else "")
            <>  "λ("
            <>  buildVar x
            <>  " : "
            <>  go False False _A 
            <>  ") → "
            <>  go False False b
            <>  (if parenBind then ")" else "")
        Pi  x _A b ->
                (if parenBind then "(" else "")
            <>  (if used x e
                 then "∀(" <> buildVar x <> " : " <> go False False _A <> ")"
                 else go True False _A )
            <>  " → "
            <>  go False False b
            <>  (if parenBind then ")" else "")
        App f a    ->
                (if parenApp then "(" else "")
            <>  go True False f <> " " <> go True True a
            <>  (if parenApp then ")" else "")

used :: Var -> Expr -> Bool
used x = go
  where
    go e = case e of
        Var x' | x == x'   -> True
               | otherwise -> False
        Lam _ _A b         -> go _A || go b
        Pi  _ _A b         -> go _A || go b
        App f a            -> go f || go a
        Const _            -> False

-- | Render an expression as pretty-printed `Text`
pretty :: Expr -> Text
pretty = toLazyText . buildExpr

freeOf :: Text -> Expr -> IntSet
freeOf txt = go
  where
    go e = case e of
        Var (V txt' n) | txt == txt' -> IntSet.singleton n
                       | otherwise   -> IntSet.empty
        Lam (V _ n   )  _ b          -> IntSet.delete n (go b)
        Pi  (V _ n   )  _ b          -> IntSet.delete n (go b)
        App f a                      -> IntSet.union (go f) (go a)
        Const _                      -> IntSet.empty

subst :: Var -> Expr -> Expr -> Expr
subst x0 e0 = go
  where
    go e = case e of
        Lam x _A b -> helper Lam x _A b
        Pi  x _A b -> helper Pi  x _A b
        App f a    -> App (go f) (go a)
        Var x      -> if (x == x0) then e0 else e
        Const _    -> e

    helper c x@(V txt n) _A b =
        if x == x0
        then c x _A b  -- x shadows x0
        else
            let fs1 = IntSet.union (freeOf txt (Var x0)) (freeOf txt e0)
            in  if IntSet.member n fs1
                then
                    let x' = V txt (IntSet.findMax fs1 + 1)
                    in  c x' (go _A) (go (subst x (Var x') b))
                else c x (go _A) (go b)

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

{-| Type-check an expression and return the expression's type if type-checking
    suceeds or an error if type-checking fails
-}
typeOf :: Expr -> Either Text Expr
typeOf = typeOf_ []

whnf :: Expr -> Expr
whnf e = case e of
    App f a -> case whnf f of
        Lam x _A b -> whnf (subst x a b)  -- Beta reduce
        _          -> e
    _       -> e

freeIn :: Var -> Expr -> Bool
freeIn x = go
  where
    go e = case e of
        Lam x' _A b -> x /= x' && (go _A || go b)
        Pi  x' _A b -> x /= x' && (go _A || go b)
        Var x'      -> x == x'
        App f a     -> go f || go a
        Const _     -> False

-- | Reduce an expression to its normal form
normalize :: Expr -> Expr
normalize e = case e of
    Lam x _A b -> case b' of
        App f a -> case normalize a of
            Var x' | x == x' && not (x `freeIn` f) -> normalize f  -- Eta reduce
                   | otherwise                     -> e'
            _                                      -> e'
        _       -> e'
      where
        b' = normalize b
        e' = Lam x (normalize _A) b'
    Pi  x _A b -> Pi  x (normalize _A) (normalize b)
    App f _C   -> case normalize f of
        Lam x _A _B -> normalize (subst x _C _B)  -- Beta reduce
        f'          -> App f' (normalize _C)
    Var   _    -> e
    Const _    -> e

-- | Convenience function to pretty-print an expression to the console
printValue :: Expr -> IO ()
printValue = Text.putStrLn . pretty

{-| Convenience function to pretty print an expression's type, or output an error
    message if type checking fails
-}
printType :: Expr -> IO ()
printType expr = case typeOf expr of
    Left err -> Text.putStr err
    Right t  -> Text.putStrLn (pretty t)
