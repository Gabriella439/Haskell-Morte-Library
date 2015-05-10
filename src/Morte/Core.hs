{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
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


    Strong normalization comes at a price: Morte forbids recursion.  Instead,
    you must translate all recursion to F-algebras and translate all corecursion
    to F-coalgebras.  If you are new to F-(co)algebras then you may wish to read
    "Morte.Tutorial" or read \"Recursive types for free!\":

    <http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt>

    Morte is designed to be a super-optimizing intermediate language with a
    simple optimization scheme.  You optimize a Morte expression by just
    normalizing the expression.  If you normalize a long-lived program encoded
    as an F-coalgebra you typically get a state machine, and if you normalize a
    long-lived program encoded as an F-algebra you typically get an unrolled
    loop.

    Strong normalization guarantees that all abstractions encodable in Morte are
    \"free\", meaning that they may increase your program's compile times but
    they will never increase your program's run time because they will normalize
    to the same code.
-}

module Morte.Core (
    -- * Syntax
    Var(..),
    Const(..),
    Path(..),
    X(..),
    Expr(..),
    Context,

    -- * Core functions
    typeWith,
    typeOf,
    normalize,

    -- * Utilities
    shift,
    pretty,

    -- * Errors
    TypeError(..),
    TypeMessage(..),
    ) where

import Control.Applicative (Applicative(pure, (<*>)), (<$>))
import Control.DeepSeq (NFData(..))
import Control.Exception (Exception)
import Control.Monad.Trans.State (evalState)
import qualified Control.Monad.Trans.State as State
import Data.Binary (Binary(..), Get, Put)
import Data.Binary.Get (getWord64le)
import Data.Binary.Put (putWord64le)
import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Data.Monoid ((<>))
import Data.String (IsString(..))
import Data.Text.Buildable (Buildable(..))
import Data.Text.Lazy (Text, unpack)
import qualified Data.Text.Encoding as Text
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Builder as Builder
import Data.Typeable (Typeable)
import Data.Word (Word8)
import Filesystem.Path.CurrentOS (FilePath)
import qualified Filesystem.Path.CurrentOS as Filesystem
import Prelude hiding (FilePath)

{-| Label for a bound variable

    The `Text` field is the variable's name (i.e. \"@x@\").

    The `Int` field disambiguates variables with the same name if there are
    multiple bound variables of the same name in scope.  Zero refers to the
    nearest bound variable and the index increases by one for each bound variable
    of the same name going outward.  The following diagram may help:

>                           +-refers to-+
>                           |           |
>                           v           |
> \(x : *) -> \(y : *) -> \(x : *) -> x@0
>
>   +-------------refers to-------------+
>   |                                   |
>   v                                   |
> \(x : *) -> \(y : *) -> \(x : *) -> x@1

    This `Int` behaves like a De Bruijn index in the special case where all
    variables have the same name.

    You can optionally omit the index if it is @0@:

>                           +refers to+
>                           |         |
>                           v         |
> \(x : *) -> \(y : *) -> \(x : *) -> x

    Zero indices are omitted when pretty-printing `Var`s and non-zero indices
    appear as a numeric suffix.
-}
data Var = V Text Int deriving (Eq, Show)

putUtf8 :: Text -> Put
putUtf8 txt = put (Text.encodeUtf8 (Text.toStrict txt))

getUtf8 :: Get Text
getUtf8 = do
    bs <- get
    case Text.decodeUtf8' bs of
        Left  e   -> fail (show e)
        Right txt -> return (Text.fromStrict txt)

instance Binary Var where
    put (V x n) = do
        putUtf8 x
        putWord64le (fromIntegral n)
    get = V <$> getUtf8 <*> fmap fromIntegral getWord64le

instance IsString Var
  where
    fromString str = V (Text.pack str) 0

instance NFData Var where
  rnf (V n p) = rnf n `seq` rnf p

instance Buildable Var where
    build (V txt n) = build txt <> if n == 0 then "" else ("@" <> build n)

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

instance NFData Const where
    rnf c = seq c ()

instance Buildable Const where
    build c = case c of
        Star -> "*"
        Box  -> "□"

axiom :: Const -> Either TypeError Const
axiom Star = return Box
axiom Box  = Left (TypeError [] (Const Box) (Untyped Box))

rule :: Const -> Const -> Either TypeError Const
rule Star Box  = return Box
rule Star Star = return Star
rule Box  Box  = return Box
rule Box  Star = return Star

-- | Path to an external resource
data Path
    = File FilePath
    | URL  String
    deriving (Eq, Ord, Show)

instance Buildable Path where
    build (File file) = "#" <> build (toText' file)
      where
        toText' = either id id . Filesystem.toText
    build (URL  str ) = "#" <> build str

{-| Like `Data.Void.Void`, except with an `NFData` instance in order to avoid
    orphan instances
-}
newtype X = X { absurd :: forall a . a }

instance Eq X where
    _ == _ = True

instance Show X where
    show = absurd

instance NFData X where
    rnf x = seq x ()

instance Buildable X where
    build = absurd

-- | Syntax tree for expressions
data Expr a
    -- | > Const c        ~  c
    = Const Const
    -- | > Var (V x 0)    ~  x
    --   > Var (V x n)    ~  x@n
    | Var Var
    -- | > Lam x     A b  ~  λ(x : A) → b
    | Lam Text (Expr a) (Expr a)
    -- | > Pi x      A B  ~  ∀(x : A) → B
    --   > Pi unused A B  ~        A  → B
    | Pi  Text (Expr a) (Expr a)
    -- | > App f a        ~  f a
    | App (Expr a) (Expr a)
    -- | > Import path    ~  #path
    | Import a
    deriving (Functor, Foldable, Traversable, Show)

instance Applicative Expr where
    pure = Import

    mf <*> mx = case mf of
        Const c     -> Const c
        Var   v     -> Var v
        Lam x _A  b -> Lam x (_A <*> mx) ( b <*> mx)
        Pi  x _A _B -> Pi  x (_A <*> mx) (_B <*> mx)
        App f a     -> App (f <*> mx) (a <*> mx)
        Import f    -> fmap f mx

instance Monad Expr where
    return = Import

    m >>= k = case m of
        Const c     -> Const c
        Var   v     -> Var v
        Lam x _A  b -> Lam x (_A >>= k) ( b >>= k)
        Pi  x _A _B -> Pi  x (_A >>= k) (_B >>= k)
        App f a     -> App (f >>= k) (a >>= k)
        Import r    -> k r

lookupN :: Eq a => a -> [(a, b)] -> Int -> Maybe b
lookupN a ((a', b'):abs') n | a /= a'   = lookupN a abs'    n
                            | n >  0    = lookupN a abs' $! n - 1
                            | n == 0    = Just b'
                            | otherwise = Nothing
lookupN _  []             _             = Nothing

lookupCtx :: Var -> Context -> Maybe (Expr X)
lookupCtx (V x n) ctx = lookupN x ctx n

match :: Text -> Int -> Text -> Int -> [(Text, Text)] -> Bool
match xL nL xR nR  []                                      = xL == xR && nL == nR
match xL 0  xR 0  ((xL', xR'):_ ) | xL == xL' && xR == xR' = True
match xL nL xR nR ((xL', xR'):xs) = nL' `seq` nR' `seq` match xL nL' xR nR' xs
  where
    nL' = if xL == xL' then nL - 1 else nL
    nR' = if xR == xR' then nR - 1 else nR

instance Eq a => Eq (Expr a) where
    eL0 == eR0 = evalState (go (normalize eL0) (normalize eR0)) []
      where
--      go :: Expr a -> Expr a -> State [(Text, Text)] Bool
        go (Const cL) (Const cR) = return (cL == cR)
        go (Var (V xL nL)) (Var (V xR nR)) = do
            ctx <- State.get
            return (match xL nL xR nR ctx)
        go (Lam xL tL bL) (Lam xR tR bR) = do
            ctx <- State.get
            State.put ((xL, xR):ctx)
            eq1 <- go tL tR
            eq2 <- go bL bR
            State.put ctx
            return (eq1 && eq2)
        go (Pi xL tL bL) (Pi xR tR bR) = do
            ctx <- State.get
            State.put ((xL, xR):ctx)
            eq1 <- go tL tR
            eq2 <- go bL bR
            State.put ctx
            return (eq1 && eq2)
        go (App fL aL) (App fR aR) = do
            b1 <- go fL fR
            b2 <- go aL aR
            return (b1 && b2)
        go (Import pL) (Import pR) = return (pL == pR)
        go _ _ = return False

instance Binary a => Binary (Expr a) where
    put e = case e of
        Const c    -> do
            put (0 :: Word8)
            put c
        Var x      -> do
            put (1 :: Word8)
            put x
        Lam x _A b -> do
            put (2 :: Word8)
            putUtf8 x
            put _A
            put b
        Pi  x _A _B -> do
            put (3 :: Word8)
            putUtf8 x
            put _A
            put _B
        App f a     -> do
            put (4 :: Word8)
            put f
            put a
        Import p    -> do
            put (5 :: Word8)
            put p

    get = do
        n <- get :: Get Word8
        case n of
            0 -> Const <$> get
            1 -> Var <$> get
            2 -> Lam <$> getUtf8 <*> get <*> get
            3 -> Pi  <$> getUtf8 <*> get <*> get
            4 -> App <$> get <*> get
            5 -> Import <$> get
            _ -> fail "get Expr: Invalid tag byte"

instance IsString (Expr a)
  where
    fromString str = Var (fromString str)

instance NFData a => NFData (Expr a) where
    rnf e = case e of
        Const c     -> rnf c
        Var   v     -> rnf v
        Lam x _A b  -> rnf x `seq` rnf _A `seq` rnf b
        Pi  x _A _B -> rnf x `seq` rnf _A `seq` rnf _B
        App f a     -> rnf f `seq` rnf a
        Import p    -> rnf p

-- | Generates a syntactically valid Morte program
instance Buildable a => Buildable (Expr a)
  where
    build = go False False
      where
        go parenBind parenApp e = case e of
            Const c    -> build c
            Var x      -> build x
            Lam x _A b ->
                    (if parenBind then "(" else "")
                <>  "λ("
                <>  build x
                <>  " : "
                <>  go False False _A
                <>  ") → "
                <>  go False False b
                <>  (if parenBind then ")" else "")
            Pi  x _A b ->
                    (if parenBind then "(" else "")
                <>  (if x /= "_"
                     then "∀(" <> build x <> " : " <> go False False _A <> ")"
                     else go True False _A )
                <>  " → "
                <>  go False False b
                <>  (if parenBind then ")" else "")
            App f a    ->
                    (if parenApp then "(" else "")
                <>  go True False f <> " " <> go True True a
                <>  (if parenApp then ")" else "")
            Import p   -> build p

{-| Bound variable names and their types

    Variable names may appear more than once in the `Context`.  The `Var` @x\@n@
    refers to the @n@th occurrence of @x@ in the `Context` (using 0-based
    numbering).
-}
type Context = [(Text, Expr X)]

-- | The specific type error
data TypeMessage
    = UnboundVariable
    | InvalidInputType (Expr X)
    | InvalidOutputType (Expr X)
    | NotAFunction
    | TypeMismatch (Expr X) (Expr X)
    | Untyped Const
    deriving (Show)

instance NFData TypeMessage where
    rnf tm = case tm of
        UnboundVariable     -> ()
        InvalidInputType e  -> rnf e
        InvalidOutputType e -> rnf e
        NotAFunction        -> ()
        TypeMismatch e1 e2  -> rnf e1 `seq` rnf e2
        Untyped c           -> rnf c

instance Buildable TypeMessage where
    build msg = case msg of
        UnboundVariable          ->
                "Error: Unbound variable\n"
        InvalidInputType expr    ->
                "Error: Invalid input type\n"
            <>  "\n"
            <>  "Type: " <> build expr <> "\n"
        InvalidOutputType expr   ->
                "Error: Invalid output type\n"
            <>  "\n"
            <>  "Type: " <> build expr <> "\n"
        NotAFunction             ->
                "Error: Only functions may be applied to values\n"
        TypeMismatch expr1 expr2 ->
                "Error: Function applied to argument of the wrong type\n"
            <>  "\n"
            <>  "Expected type: " <> build expr1 <> "\n"
            <>  "Argument type: " <> build expr2 <> "\n"
        Untyped c                ->
                "Error: " <> build c <> " has no type\n"

-- | A structured type error that includes context
data TypeError = TypeError
    { context     :: Context
    , current     :: Expr X
    , typeMessage :: TypeMessage
    } deriving (Typeable)

instance Show TypeError where
    show = unpack . pretty

instance Exception TypeError

instance NFData TypeError where
    rnf (TypeError ctx crr tym) = rnf ctx `seq` rnf crr `seq` rnf tym

instance Buildable TypeError where
    build (TypeError ctx expr msg)
        =   "\n"
        <>  (    if Text.null (Builder.toLazyText (buildContext ctx))
                 then ""
                 else "Context:\n" <> buildContext ctx <> "\n"
            )
        <>  "Expression: " <> build expr <> "\n"
        <>  "\n"
        <>  build msg
      where
        buildKV (key, val) = build key <> " : " <> build val

        buildContext =
                Builder.fromLazyText
            .   Text.unlines
            .   map (Builder.toLazyText . buildKV)
            .   reverse

{-| Substitute all occurrences of a variable with an expression

> subst x n C B  ~  B[x@n := C]
-}
subst :: Text -> Int -> Expr a -> Expr a -> Expr a
subst x n e' e = case e of
    Lam x' _A  b  -> Lam x' (subst x n e' _A)  b'
      where
        n'  = if x == x' then n + 1 else n
        b'  = n' `seq` subst x n' (shift 1 x' e')  b
    Pi  x' _A _B  -> Pi  x' (subst x n e' _A) _B'
      where
        n'  = if x == x' then n + 1 else n
        _B' = n' `seq` subst x n' (shift 1 x' e') _B
    App f a       -> App (subst x n e' f) (subst x n e' a)
    Var (V x' n') -> if x == x' && n == n' then e' else e
    Const k       -> Const k
    -- This assumes that all imports are closed expressions
    Import p      -> Import p

{-| @shift n x@ adds @n@ to the index of all free variables named @x@ within an
    `Expr`
-}
shift :: Int -> Text -> Expr a -> Expr a
shift d x0 e0 = go e0 0
  where
    go e c = case e of
        Lam x _A  b  -> Lam x (go _A c) (go  b $! c')
          where
            c' = if x == x0 then c + 1 else c
        Pi  x _A _B  -> Pi  x (go _A c) (go _B $! c')
          where
            c' = if x == x0 then c + 1 else c
        App f a       -> App (go f c) (go a c)
        Var (V x n) -> n' `seq` Var (V x n')
          where
            n' = if x == x0 && n >= c then n + d else n
        Const k       -> Const k
        -- This assumes that all imports are closed expressions
        Import p      -> Import p

{-| Type-check an expression and return the expression's type if type-checking
    suceeds or an error if type-checking fails

    `typeWith` does not necessarily normalize the type since full normalization
    is not necessary for just type-checking.  If you actually care about the
    returned type then you may want to `normalize` it afterwards.
-}
typeWith :: Context -> Expr X -> Either TypeError (Expr X)
typeWith ctx e = case e of
    Const c     -> fmap Const (axiom c)
    Var x       -> case lookupCtx x ctx of
        Nothing -> Left (TypeError ctx e UnboundVariable)
        Just a  -> return a
    Lam x _A b  -> do
        let ctx' = [ (x', shift 1 x _A') | (x', _A') <- (x, _A):ctx ]
        _B <- typeWith ctx' b
        let p = Pi x _A _B
        _t <- typeWith ctx p
        return p
    Pi  x _A _B -> do
        eS <- fmap whnf (typeWith ctx _A)
        s  <- case eS of
            Const s -> return s
            _       -> Left (TypeError ctx e (InvalidInputType _A))
        let ctx' = [ (x', shift 1 x _A') | (x', _A') <- (x, _A):ctx ]
        eT <- fmap whnf (typeWith ctx' _B)
        t  <- case eT of
            Const t -> return t
            _       -> Left (TypeError ctx' e (InvalidOutputType _B))
        fmap Const (rule s t)
    App f a     -> do
        e' <- fmap whnf (typeWith ctx f)
        (x, _A, _B) <- case e' of
            Pi x _A _B -> return (x, _A, _B)
            _          -> Left (TypeError ctx e NotAFunction)
        _A' <- typeWith ctx a
        if _A == _A'
            then do
                let a'  = shift 1 x a
                    _B' = subst x 0 a' _B
                return (shift (-1) x _B')
            else do
                let nf_A  = normalize _A
                    nf_A' = normalize _A'
                Left (TypeError ctx e (TypeMismatch nf_A nf_A'))
    Import p    -> absurd p

{-| `typeOf` is the same as `typeWith` with an empty context, meaning that the
    expression must be closed (i.e. no free variables), otherwise type-checking
    will fail.
-}
typeOf :: Expr X -> Either TypeError (Expr X)
typeOf = typeWith []

-- | Reduce an expression to weak-head normal form
whnf :: Expr a -> Expr a
whnf e = case e of
    App f a -> case whnf f of
        Lam x _A b -> whnf (shift (-1) x b')  -- Beta reduce
          where
            a' = shift 1 x a
            b' = subst x 0 a' b
        _          -> e
    _       -> e

-- | Returns whether a variable is free in an expression
freeIn :: Var -> Expr a -> Bool
freeIn v@(V x n) = go
  where
    go e = case e of
        Lam x' _A b  ->
            n' `seq` (go _A || if x == x' then freeIn (V x n')  b else go  b)
          where
            n' = n + 1
        Pi  x' _A _B ->
            n' `seq` (go _A || if x == x' then freeIn (V x n') _B else go _B)
          where
            n' = n + 1
        Var v'      -> v == v'
        App f a     -> go f || go a
        Const _     -> False
        -- This assumes that all imports are closed expressions
        Import _    -> False

{-| Reduce an expression to its normal form, performing both beta reduction and
    eta reduction

    `normalize` does not type-check the expression.  You may want to type-check
    expressions before normalizing them since normalization can convert an
    ill-typed expression into a well-typed expression.
-}
normalize :: Expr a -> Expr a
normalize e = case e of
    Lam x _A b -> case b' of
        App f a -> case a of
            Var v' | v == v' && not (v `freeIn` f) ->
                shift (-1) x f  -- Eta reduce
                   | otherwise                     ->
                e'
              where
                v = V x 0
            _                                      -> e'
        _       -> e'
      where
        b' = normalize b
        e' = Lam x (normalize _A) b'
    Pi  x _A _B -> Pi x (normalize _A) (normalize _B)
    App f a     -> case normalize f of
        Lam x _A b -> normalize (shift (-1) x b')  -- Beta reduce
          where
            a' = shift 1 x (normalize a)
            b' = subst x 0 a' b
        f'         -> App f' (normalize a)
    Var   _    -> e
    Const _    -> e
    Import p   -> Import p

-- | Pretty-print a value
pretty :: Buildable a => a -> Text
pretty = Builder.toLazyText . build
