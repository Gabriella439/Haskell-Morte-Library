{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}

{-| Morte is a typed, purely functional, and strongly normalizing term rewriting
    system designed as an intermediate language for compilers.  Use this library
    to type-check, normalize, parse, pretty-print, serialize and deserialize
    expressions in this intermediate language.


    This module contains the core calculus for the Morte language.  This language
    is a minimalist implementation of the calculus of constructions, which is in
    turn a specific kind of pure type system.  If you are new to pure type
    systems you may wish to read:
    <http://research.microsoft.com/en-us/um/people/simonpj/papers/henk.ps.gz Henk: a typed intermediate language>.


    Morte is a strongly normalizing language, meaning that:

    * Every expression has a unique normal form computed by `normalize`
    * You test expressions for equality of their normal forms using `==`
    * Equational reasoning preserves normal forms


    If you strongly normalize every expression then:

    * Equal expressions generate identical machine code
    * You only pay for all abstraction at compile-time instead of run-time


    Strong normalization comes at a price: Morte forbids recursion.  Instead, you
    must translate all recursion to F-algebras and translate all corecursion to
    F-coalgebras.  If you are new to F-(co)algebras then you may wish to read:
    <http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt Recursive types for free!>

-}

module Morte (
    -- * Syntax
    Var(..),
    Const(..),
    Expr(..),

    -- * Errors
    Context,
    TypeMessage(..),
    TypeError(..),

    -- * Core operations
    typeOf,
    normalize,

    -- * Utilities
    parse,
    pretty,
    explain,
    printValue,
    printType,
    ) where

import Control.Applicative (pure, (<$>), (<*>), (*>), (<*), (<|>))
import Control.Exception (Exception)
import Control.Monad (void)
import Control.Monad.Trans.State (State, evalState, get, modify)
import qualified Data.Attoparsec.Text.Lazy as A
import Data.Attoparsec.Text.Lazy (Parser)
import Data.Char (isSpace)
import Data.Monoid (mempty, (<>))
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.String (IsString(fromString))
import Data.Text ()  -- For the `IsString` instance
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.IO as Text
import Data.Text.Lazy.Builder (Builder, toLazyText, fromLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import Data.Typeable (Typeable)

-- TODO: Include example use cases in module header
-- TODO: Add `Binary` instance
-- TODO: Document all functions

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

axiom :: Const -> Either TypeError Const
axiom Star = return Box
axiom Box  = Left (TypeError [] (Const Box) (Untyped Box))

rule :: Const -> Const -> Either TypeError Const
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

-- | Bound variables and their types
type Context = [(Var, Expr)]

-- | The specific type error
data TypeMessage
    = UnboundVariable
    | InvalidInputType Expr
    | InvalidOutputType Expr
    | NotAFunction
    | TypeMismatch Expr Expr
    | Untyped Const
    deriving (Show, Typeable)

-- | A structured type error that includes context
data TypeError = TypeError
    { context :: Context
    , current :: Expr
    , message :: TypeMessage
    } deriving (Show, Typeable)

instance Exception TypeError

buildConst :: Const -> Builder
buildConst c = case c of
    Star -> "*"
    Box  -> "□"

buildVar :: Var -> Builder
buildVar (V txt n) = fromLazyText txt <> if n == 0 then mempty else decimal n

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
    used x = go'
      where
        go' e = case e of
            Var x' | x == x'   -> True
                   | otherwise -> False
            Lam _ _A b         -> go' _A || go' b
            Pi  _ _A b         -> go' _A || go' b
            App f a            -> go' f || go' a
            Const _            -> False

buildTypeMessage :: TypeMessage -> Builder
buildTypeMessage msg = case msg of
    UnboundVariable          ->
            "Error: Unbound variable\n"
    InvalidInputType expr    ->
            "Error: Invalid input type\n"
        <>  "\n"
        <>  "Type: " <> buildExpr expr <> "\n"
    InvalidOutputType expr   ->
            "Error: Invalid output type\n"
        <>  "\n"
        <>  "Type: " <> buildExpr expr <> "\n"
    NotAFunction             ->
            "Error: Only functions may be applied to values\n"
    TypeMismatch expr1 expr2 ->
            "Error: Function applied to argument of the wrong type\n"
        <>  "\n"
        <>  "Expected type: " <> buildExpr expr1 <> "\n"
        <>  "Argument type: " <> buildExpr expr2 <> "\n"
    Untyped c                ->
            "Error: " <> buildConst c <> " has no type\n"

buildTypeError :: TypeError -> Builder
buildTypeError (TypeError ctx expr msg)
    =   (    if Text.null (toLazyText buildContext )
             then mempty
             else "Context:\n" <> buildContext <> "\n"
        )
    <>  "Expression: " <> buildExpr expr <> "\n"
    <>  "\n"
    <>  buildTypeMessage msg
  where
    buildKV (key, val) = buildVar key <> " : " <> buildExpr val

    buildContext =
        (fromLazyText . Text.unlines . map (toLazyText . buildKV) . reverse) ctx


-- | Render an expression as pretty-printed `Text`
pretty :: Expr -> Text
pretty = toLazyText . buildExpr

-- | Render a type error as pretty-printed `Text`
explain :: TypeError -> Text
explain = toLazyText . buildTypeError

-- | Find all free variables with a given label and return their numeric suffixes
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

-- | Substitute all occurrences of a variable with an expression
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
            let fs = IntSet.union (freeOf txt (Var x0)) (freeOf txt e0)
            in  if IntSet.member n fs
                then
                    let x' = V txt (IntSet.findMax fs + 1)
                    in  c x' (go _A) (go (subst x (Var x') b))
                else c x (go _A) (go b)

-- | Compute the type of an expression, given a context
typeOf_ :: Context -> Expr -> Either TypeError Expr
typeOf_ ctx e = case e of
    Const c  -> fmap Const (axiom c)
    Var x    -> case lookup x ctx of
        Nothing -> Left (TypeError ctx e UnboundVariable)
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
            _       -> Left (TypeError ctx e (InvalidInputType _A))
        let ctx' = (x, _A):ctx
        eT <- fmap whnf (typeOf_ ctx' _B)
        t  <- case eT of
            Const t -> return t
            _       -> Left (TypeError ctx' e (InvalidOutputType _B))
        fmap Const (rule s t)
    App f a  -> do
        e' <- fmap whnf (typeOf_ ctx f)
        (x, _A, _B) <- case e' of
            Pi x _A _B -> return (x, _A, _B)
            _          -> Left (TypeError ctx e NotAFunction)
        _A' <- typeOf_ ctx a
        let nf_A  = normalize _A 
            nf_A' = normalize _A'
        if nf_A == nf_A'
            then return (subst x a _B)
            else Left (TypeError ctx e (TypeMismatch nf_A nf_A'))

{-| Type-check an expression and return the expression's type if type-checking
    suceeds or an error if type-checking fails

    The expression must be closed (no free variables), otherwise type-checking
    will fail.

    `typeOf` does not necessarily normalize the type.
-}
typeOf :: Expr -> Either TypeError Expr
typeOf = typeOf_ []

-- | Reduce an expression to weak-head normal form
whnf :: Expr -> Expr
whnf e = case e of
    App f a -> case whnf f of
        Lam x _A b -> whnf (subst x a b)  -- Beta reduce
        _          -> e
    _       -> e

-- | Returns whether a variable is free in an expression
freeIn :: Var -> Expr -> Bool
freeIn x = go
  where
    go e = case e of
        Lam x' _A b -> x /= x' && (go _A || go b)
        Pi  x' _A b -> x /= x' && (go _A || go b)
        Var x'      -> x == x'
        App f a     -> go f || go a
        Const _     -> False

{-| Reduce an expression to its normal form

    `normalize` does not type-check the expression.
-}
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

{-| Convenience function to pretty-print an expression to the console

    `printValue` does not type-check or normalize the expression.
-}
printValue :: Expr -> IO ()
printValue = Text.putStrLn . pretty

{-| Convenience function to pretty print an expression's type, or output an error
    message if type checking fails

    `printType` does not necessarily normalize the type.
-}
printType :: Expr -> IO ()
printType expr = case typeOf expr of
    Left err -> Text.putStr (explain err)
    Right t  -> Text.putStrLn (pretty t)

-- | Parser for a single expression
parse :: Parser Expr
parse = A.skipSpace *> parseExpr <* A.skipSpace

parseExpr :: Parser Expr
parseExpr = parseLam <|> parsePi <|> parseBExpr

parsePi :: Parser Expr
parsePi = parseBind Pi skipPi <|> parsePiSimple

parsePiSimple :: Parser Expr
parsePiSimple =
        Pi "_"
    <$> (parseBExpr <* A.skipSpace)
    <*> (   (skipArrow  <* A.skipSpace)
        *>   parseExpr
        )

parseLam :: Parser Expr
parseLam = parseBind Lam skipLambda

parseBind :: (Var -> Expr -> Expr -> Expr) -> Parser () -> Parser Expr
parseBind c symbol =
        c
    <$> (   (symbol     <* A.skipSpace)
        *>  (A.char '(' <* A.skipSpace)
        *>  (parseVar   <* A.skipSpace)
        )
    <*> (   (A.char ':' <* A.skipSpace)
        *>  (parseExpr  <* A.skipSpace)
        )
    <*> (   (A.char ')' <* A.skipSpace)
        *>  (skipArrow  <* A.skipSpace)
        *>   parseExpr
        )

skipLambda :: Parser ()
skipLambda =
        void (A.char   'λ'  )
    <|> void (A.char   'Λ'  )
    <|> void (A.char   '\\' )
    <|> void (A.string "/\\")

skipPi :: Parser ()
skipPi =
        void (A.char   '∀'      )
    <|> void (A.char   'Π'      )
    <|> void (A.string "|~|"    )
    <|> void (A.string "\\/"    )
    <|> void (A.string "forall ")

skipArrow :: Parser ()
skipArrow =
        void (A.char   '→' )
    <|> void (A.string "->")

parseBExpr :: Parser Expr
parseBExpr = foldr1 App <$> A.sepBy1 parseAExpr (A.space *> A.skipSpace)

parseAExpr :: Parser Expr
parseAExpr =
        A.char '(' *> A.skipSpace *> parseExpr <* A.char ')'
    <|> parseConst
    <|> Var <$> parseVar

parseVar :: Parser Var
parseVar = V <$> txt <*> n
 where
    p c =   not (isSpace c)
        &&  c /= '('
        &&  c /= ')'
        &&  c /= '@'
        &&  c /= '-'
        &&  c /= '→'
    txt = Text.fromStrict <$> A.takeWhile1 p
    n   = A.char '@' *> A.decimal <|> pure 0

parseConst :: Parser Expr
parseConst =
        Const
    <$> (    A.string "*" *> pure Star
        <|> (void (A.string "BOX") <|> void (A.char '□')) *> pure Box
        )
