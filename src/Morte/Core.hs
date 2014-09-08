{-# LANGUAGE OverloadedStrings, DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wall #-}

{-| This module contains the core calculus for the Morte language.  This
    language is a minimalist implementation of the calculus of constructions,
    which is in turn a specific kind of pure type system.  If you are new to
    pure type systems you may wish to read \"Henk: a typed intermediate
    language\".

    <http://research.microsoft.com/en-us/um/people/simonpj/papers/henk.ps.gz>


    Morte is a strongly normalizing language, meaning that:

    * Every expression has a unique normal form computed by `normalize`

    * You test expressions for equality of their normal forms using `==`

    * Equational reasoning preserves normal forms


    Strong normalization comes at a price: Morte forbids recursion, which is
    syntactically unrepresentable.  Instead, you must translate all recursion to
    F-algebras and translate all corecursion to F-coalgebras.  If you are new to
    F-(co)algebras then you may wish to read \"Recursive types for free!\":

    <http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt>

    Morte is designed to be a super-optimizing intermediate language with a
    simple optimization scheme.  You optimize a Morte expression by just
    normalizing the expression.  If you normalize an F-coalgebra you get an
    ordinary loop, and if you normalize an F-algebra you get an unrolled loop.

    Strong normalization guarantees that all abstractions encodable in Morte are
    \"free\", meaning that they may increase your program's compile times but
    they will never increase your program's run time because they will normalize
    to the same code.
-}

module Morte.Core (
    -- * Syntax
    Var(..),
    Const(..),
    Expr(..),
    Context,

    -- * Core functions
    typeWith,
    typeOf,
    normalize,

    -- * Utilities
    prettyExpr,
    prettyTypeError,

    -- * Errors
    TypeError(..),
    TypeMessage(..)
    ) where

import Control.Applicative ((<$>), (<*>))
import Control.Exception (Exception)
import Control.Monad.Trans.State (State, evalState, modify)
import qualified Control.Monad.Trans.State as State
import Data.Binary (Binary(get, put), Get)
import Data.Binary.Get (getWord64le)
import Data.Binary.Put (putWord64le)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Monoid (mempty, (<>))
import Data.String (IsString(fromString))
import Data.Text ()  -- For the `IsString` instance
import Data.Text.Lazy (Text)
import qualified Data.Text.Encoding as Text
import qualified Data.Text.Lazy as Text
import Data.Text.Lazy.Builder (Builder, toLazyText, fromLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import Data.Typeable (Typeable)
import Data.Word (Word8)

-- TODO: Include example use cases in module header

{-| Label for a bound variable

    The `Text` field is the variable's name.

    The `Int` field disambiguates variables with the same name.  Zero is a good
    default.  Non-zero values will appear as a numeric suffix when
    pretty-printing the `Var`.
-}
data Var = V Text Int deriving (Eq, Show)

instance Binary Var where
    put (V txt n) = do
        put (Text.encodeUtf8 (Text.toStrict txt))
        putWord64le (fromIntegral n)
    get = do
        bs <- get
        case Text.decodeUtf8' bs of
            Left  e   ->
                fail (show e)
            Right txt ->
                V (Text.fromStrict txt) <$> fmap fromIntegral getWord64le

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

instance Binary Const where
    put c = case c of
        Star -> put (0 :: Word8)
        Box  -> put (1 :: Word8)
    get = do
        n <- get :: Get Word8
        case n of
            0 -> return Star
            1 -> return Box
            _ -> fail "get Const: Invalid tag byte"

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
    --   > Var (V x n)    ~  x@n
    | Var Var
    -- | > Lam x     A b  ~  λ(x : A) → b
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
            ctx <- State.get
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

instance Binary Expr where
    put e = case e of
        Const c    -> do
            put (0 :: Word8)
            put c
        Var x      -> do
            put (1 :: Word8)
            put x
        Lam x _A b -> do
            put (2 :: Word8)
            put x
            put _A
            put b
        Pi  x _A _B -> do
            put (3 :: Word8)
            put x
            put _A
            put _B
        App f a     -> do
            put (4 :: Word8)
            put f
            put a

    get = do
        n <- get :: Get Word8
        case n of
            0 -> Const <$> get
            1 -> Var <$> get
            2 -> Lam <$> get <*> get <*> get
            3 -> Pi  <$> get <*> get <*> get
            4 -> App <$> get <*> get
            _ -> fail "get Expr: Invalid tag byte"

instance IsString Expr
  where
    fromString str = Var (fromString str)

{-| Bound variables and their types

    Earlier `Var`s shadow later matching `Var`s
-}
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
buildVar (V txt n) =
    fromLazyText txt <> if n == 0 then mempty else "@" <> decimal n

-- | Render a pretty-printed expression as a `Builder`
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


{-| Find all free variables with a given label and return their `Int`s

    Use this to generate a new variable which does not clash with existing free
    variables
-}
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

{-| Substitute all occurrences of a variable with an expression

> subst x C B  ~  B[x := C]
-}
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

{-| Type-check an expression and return the expression's type if type-checking
    suceeds or an error if type-checking fails

    `typeWith` does not necessarily normalize the type since full normalization
    is not necessary for just type-checking.  If you actually care about the
    returned type then you may want to `normalize` it afterwards.
-}
typeWith :: Context -> Expr -> Either TypeError Expr
typeWith ctx e = case e of
    Const c  -> fmap Const (axiom c)
    Var x    -> case lookup x ctx of
        Nothing -> Left (TypeError ctx e UnboundVariable)
        Just a  -> return a
    Lam x _A b -> do
        _B <- typeWith ((x, _A):ctx) b
        let p = Pi x _A _B
        _t <- typeWith ctx p
        return p
    Pi  x _A _B -> do
        eS <- fmap whnf (typeWith ctx _A)
        s  <- case eS of
            Const s -> return s
            _       -> Left (TypeError ctx e (InvalidInputType _A))
        let ctx' = (x, _A):ctx
        eT <- fmap whnf (typeWith ctx' _B)
        t  <- case eT of
            Const t -> return t
            _       -> Left (TypeError ctx' e (InvalidOutputType _B))
        fmap Const (rule s t)
    App f a  -> do
        e' <- fmap whnf (typeWith ctx f)
        (x, _A, _B) <- case e' of
            Pi x _A _B -> return (x, _A, _B)
            _          -> Left (TypeError ctx e NotAFunction)
        _A' <- typeWith ctx a
        let nf_A  = normalize _A 
            nf_A' = normalize _A'
        if nf_A == nf_A'
            then return (subst x a _B)
            else Left (TypeError ctx e (TypeMismatch nf_A nf_A'))

{-| `typeOf` is the same as `typeWith` with an empty context, meaning that the
    expression must be closed (i.e. no free variables), otherwise type-checking
    will fail.
-}
typeOf :: Expr -> Either TypeError Expr
typeOf = typeWith []

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

{-| Reduce an expression to its normal form, performing both beta reduction and
    eta reduction

    `normalize` does not type-check the expression.  You may want to type-check
    expressions before normalizing them since normalization can convert an
    ill-typed expression into a well-typed expression.
-}
normalize :: Expr -> Expr
normalize e = case e of
    Lam x _A b -> case b' of
        App f a -> case a of
            Var x' | x == x' && not (x `freeIn` f) -> f  -- Eta reduce
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

{-| Pretty-print an expression

    The result is syntactically valid Morte code
-}
prettyExpr :: Expr -> Text
prettyExpr = toLazyText . buildExpr

-- | Pretty-print a type error
prettyTypeError :: TypeError -> Text
prettyTypeError = toLazyText . buildTypeError
