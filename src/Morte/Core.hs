{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
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
    subst,
    pretty,

    -- * Errors
    TypeError(..),
    TypeMessage(..),
    ) where

import Control.Applicative (Applicative(pure, (<*>)), (<$>))
import Control.DeepSeq (NFData(..))
import Control.Exception (Exception)
import Control.Monad (mzero)
import Control.Monad.Trans.State (evalState)
import qualified Control.Monad.Trans.State as State
import Data.Binary (Binary(..), Get, Put)
import Data.Binary.Get (getWord64le)
import Data.Binary.Put (putWord64le)
import Data.Foldable (Foldable(..))
import Data.Monoid ((<>))
import Data.String (IsString(..))
import Data.Text.Buildable (Buildable(..))
import Data.Text.Lazy (Text, unpack)
import qualified Data.Text.Encoding as Text
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Builder as Builder
import Data.Traversable (Traversable(..))
import Data.Typeable (Typeable)
import Data.Word (Word8)
import Filesystem.Path.CurrentOS (FilePath)
import qualified Filesystem.Path.CurrentOS as Filesystem
import Morte.Context (Context)
import Prelude hiding (FilePath, lookup, succ)

import qualified Morte.Context as Context

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
axiom Box  = Left (TypeError Context.empty (Const Box) (Untyped Box))

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
    build (File file) = "#" <> build (toText' file) <> " "
      where
        toText' = either id id . Filesystem.toText
    build (URL  str ) = "#" <> build str <> " "

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

instance Binary X where
    get = mzero
    put = absurd

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

    -- | > NatLit n       ~  n
    | NatLit Int
    -- | > Nat            ~  Nat
    | Nat
    -- | > FromNat        ~  fromNat
    | FromNat
    -- | > ToNat          ~  toNat
    | ToNat

    -- | > ListLit a [xs] ~ [nil a, xs]
    | ListLit (Expr a) [Expr a]
    -- | > List           ~ List
    | List
    -- | > FromList       ~ fromList
    | FromList
    -- | > ToList         ~ toList
    | ToList

    -- | > Embed path     ~  #path
    | Embed a
    deriving (Functor, Foldable, Traversable, Show)

instance Applicative Expr where
    pure = Embed

    mf <*> mx = case mf of
        Const c      -> Const c
        Var   v      -> Var v
        Lam x _A  b  -> Lam x (_A <*> mx) ( b <*> mx)
        Pi  x _A _B  -> Pi  x (_A <*> mx) (_B <*> mx)
        App f a      -> App (f <*> mx) (a <*> mx)
        NatLit n     -> NatLit n
        Nat          -> Nat
        FromNat      -> FromNat
        ToNat        -> ToNat 
        ListLit t xs -> ListLit (t <*> mx) (map (\x -> x <*> mx) xs)
        List         -> List
        FromList     -> FromList
        ToList       -> ToList
        Embed f      -> fmap f mx

instance Monad Expr where
    return = Embed

    m >>= k = case m of
        Const c      -> Const c
        Var   v      -> Var v
        Lam x _A  b  -> Lam x (_A >>= k) ( b >>= k)
        Pi  x _A _B  -> Pi  x (_A >>= k) (_B >>= k)
        App f a      -> App (f >>= k) (a >>= k)
        NatLit n     -> NatLit n
        Nat          -> Nat
        FromNat      -> FromNat
        ToNat        -> ToNat
        ListLit t xs -> ListLit (t >>= k) (map (\x -> x >>= k) xs)
        List         -> List
        FromList     -> FromList
        ToList       -> ToList
        Embed r      -> k r

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
        go (Var (V xL nL)) (Var (V xR nR))   = do
            ctx <- State.get
            return (match xL nL xR nR ctx)
        go (Lam xL tL bL) (Lam xR tR bR)     = do
            ctx <- State.get
            eq1 <- go tL tR
            State.put ((xL, xR):ctx)
            eq2 <- go bL bR
            State.put ctx
            return (eq1 && eq2)
        go (Pi xL tL bL) (Pi xR tR bR)       = do
            ctx <- State.get
            eq1 <- go tL tR
            State.put ((xL, xR):ctx)
            eq2 <- go bL bR
            State.put ctx
            return (eq1 && eq2)
        go (App fL aL) (App fR aR)           = do
            b1 <- go fL fR
            b2 <- go aL aR
            return (b1 && b2)
        go (NatLit nL) (NatLit nR)           = return (nL == nR)
        go  Nat         Nat                  = return True
        go  FromNat     FromNat              = return True
        go  ToNat       ToNat                = return True
        go (ListLit tL xsL) (ListLit tR xsR) = return (tL == tR && xsL == xsR)
        go  List             List            = return True
        go  FromList         FromList        = return True
        go  ToList           ToList          = return True
        go (Embed pL) (Embed pR) = return (pL == pR)
        go _ _ = return False

instance Binary a => Binary (Expr a) where
    put e = case e of
        Const c      -> do
            put (0 :: Word8)
            put c
        Var x        -> do
            put (1 :: Word8)
            put x
        Lam x _A b   -> do
            put (2 :: Word8)
            putUtf8 x
            put _A
            put b
        Pi  x _A _B  -> do
            put (3 :: Word8)
            putUtf8 x
            put _A
            put _B
        App f a      -> do
            put (4 :: Word8)
            put f
            put a
        Embed p      -> do
            put (5 :: Word8)
            put p
        NatLit n     -> do
            put (6 :: Word8)
            put n
        Nat          -> do
            put (7 :: Word8)
        FromNat     -> do
            put (8 :: Word8)
        ToNat        -> do
            put (9 :: Word8)
        ListLit t xs -> do
            put (10 :: Word8)
            put t
            put xs
        List         -> do
            put (11 :: Word8)
        FromList     -> do
            put (12 :: Word8)
        ToList       -> do
            put (13 :: Word8)

    get = do
        n <- get :: Get Word8
        case n of
            0  -> Const <$> get
            1  -> Var <$> get
            2  -> Lam <$> getUtf8 <*> get <*> get
            3  -> Pi  <$> getUtf8 <*> get <*> get
            4  -> App <$> get <*> get
            5  -> Embed <$> get
            6  -> NatLit <$> get
            7  -> pure Nat
            8  -> pure FromNat
            9  -> pure ToNat
            10 -> ListLit <$> get <*> get
            11 -> pure List
            12 -> pure FromList
            13 -> pure ToList
            _ -> fail "get Expr: Invalid tag byte"

instance IsString (Expr a)
  where
    fromString str = Var (fromString str)

instance NFData a => NFData (Expr a) where
    rnf e = case e of
        Const c      -> rnf c
        Var   v      -> rnf v
        Lam x _A b   -> rnf x `seq` rnf _A `seq` rnf b
        Pi  x _A _B  -> rnf x `seq` rnf _A `seq` rnf _B
        App f a      -> rnf f `seq` rnf a
        NatLit n     -> rnf n
        Nat          -> ()
        FromNat      -> ()
        ToNat        -> ()
        ListLit t xs -> rnf t `seq` rnf xs
        List         -> ()
        FromList     -> ()
        ToList       -> ()
        Embed p      -> rnf p

-- | Generates a syntactically valid Morte program
instance Buildable a => Buildable (Expr a)
  where
    build = go False False
      where
        go parenBind parenApp e = case e of
            Const c      -> build c
            Var x        -> build x
            Lam x _A b   ->
                    (if parenBind then "(" else "")
                <>  "λ("
                <>  build x
                <>  " : "
                <>  go False False _A
                <>  ") → "
                <>  go False False b
                <>  (if parenBind then ")" else "")
            Pi  x _A b   ->
                    (if parenBind then "(" else "")
                <>  (if x /= "_"
                     then "∀(" <> build x <> " : " <> go False False _A <> ")"
                     else go True False _A )
                <>  " → "
                <>  go False False b
                <>  (if parenBind then ")" else "")
            App f a      ->
                    (if parenApp then "(" else "")
                <>  go True False f <> " " <> go True True a
                <>  (if parenApp then ")" else "")
            NatLit n     -> build n
            Nat          -> "#Nat"
            FromNat      -> "#fromNat"
            ToNat        -> "#toNat"
            ListLit t xs ->
                    "[nil "
                <>  build t
                <>  mconcat (map (\x -> ", " <> build x) xs)
                <>  "]"
            List         -> "#List"
            FromList     -> "#fromList"
            ToList       -> "#toList"
            Embed p      -> build p

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
    { context     :: Context (Expr X)
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
                build
            .   Text.unlines
            .   map (Builder.toLazyText . buildKV)
            .   reverse
            .   Context.toList

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
    NatLit m      -> NatLit m
    Nat           -> Nat
    FromNat       -> FromNat
    ToNat         -> ToNat
    ListLit t xs  -> ListLit (subst x n e' t) (map (subst x n e') xs)
    List          -> List
    FromList      -> FromList
    ToList        -> ToList
    -- The Morte compiler enforces that all embedded values
    -- are closed expressions
    Embed p       -> Embed p

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
        App f a      -> App (go f c) (go a c)
        Var (V x n)  -> n' `seq` Var (V x n')
          where
            n' = if x == x0 && n >= c then n + d else n
        Const k      -> Const k
        NatLit n     -> NatLit n
        Nat          -> Nat
        FromNat      -> FromNat
        ToNat        -> ToNat
        ListLit t xs -> ListLit (go t c) (map (\x -> go x c) xs)
        List         -> List
        FromList     -> FromList
        ToList       -> ToList
        -- The Morte compiler enforces that all embedded values
        -- are closed expressions
        Embed p     -> Embed p

{-| Type-check an expression and return the expression's type if type-checking
    suceeds or an error if type-checking fails

    `typeWith` does not necessarily normalize the type since full normalization
    is not necessary for just type-checking.  If you actually care about the
    returned type then you may want to `normalize` it afterwards.
-}
typeWith :: Context (Expr X) -> Expr X -> Either TypeError (Expr X)
typeWith ctx e = case e of
    Const c      -> fmap Const (axiom c)
    Var (V x n)  -> case Context.lookup x n ctx of
        Nothing -> Left (TypeError ctx e UnboundVariable)
        Just a  -> return a
    Lam x _A b   -> do
        let ctx' = fmap (shift 1 x) (Context.insert x _A ctx)
        _B <- typeWith ctx' b
        let p = Pi x _A _B
        _t <- typeWith ctx p
        return p
    Pi  x _A _B  -> do
        eS <- fmap whnf (typeWith ctx _A)
        s  <- case eS of
            Const s -> return s
            _       -> Left (TypeError ctx e (InvalidInputType _A))
        let ctx' = fmap (shift 1 x) (Context.insert x _A ctx)
        eT <- fmap whnf (typeWith ctx' _B)
        t  <- case eT of
            Const t -> return t
            _       -> Left (TypeError ctx' e (InvalidOutputType _B))
        fmap Const (rule s t)
    App f a      -> do
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
    NatLit _     -> return Nat
    Nat          -> return (Const Star)
    FromNat      -> return (Pi "_" Nat     natType)
    ToNat        -> return (Pi "_" natType Nat    )
    ListLit a xs -> do
        let check x = do
                a' <- typeWith ctx x
                if a == a'
                    then return ()
                    else Left (TypeError ctx e (TypeMismatch a a'))
        mapM_ check xs
        return (App List a)
    List         -> return (Pi "_" (Const Star) (Const Star))
    FromList     -> do
        return (Pi "a" (Const Star) (Pi "_" (App List "a") (listType "a")))
    ToList       -> do
        return (Pi "a" (Const Star) (Pi "_" (listType "a") (App List "a")))
    Embed p      -> absurd p

{-| `typeOf` is the same as `typeWith` with an empty context, meaning that the
    expression must be closed (i.e. no free variables), otherwise type-checking
    will fail.
-}
typeOf :: Expr X -> Either TypeError (Expr X)
typeOf = typeWith Context.empty

-- | Reduce an expression to weak-head normal form
whnf :: Expr a -> Expr a
whnf e = case e of
    App f a -> case whnf f of
        Lam x _A b -> whnf (shift (-1) x b')  -- Beta reduce
          where
            a' = shift 1 x a
            b' = subst x 0 a' b
        FromNat        -> case a of
            NatLit n -> case fromNat n of
                Just e1 -> whnf e1
                Nothing -> App FromNat a
            _        -> App FromNat a
        ToNat          -> case toNat (normalize a) of
            Just n  -> NatLit n
            Nothing -> App ToNat a
        App FromList t -> case whnf a of
            ListLit t' xs -> whnf (fromList (t', xs))
            _             -> App (App FromList t) a
        App ToList   t -> case Morte.Core.toList (normalize a) of
            Just (t', xs) -> ListLit t' xs
            Nothing       -> App (App ToList t) a
        _          -> e

    _       -> e

-- | Returns whether a variable is free in an expression
freeIn :: Var -> Expr a -> Bool
freeIn v@(V x n) = go
  where
    go e = case e of
        Lam x' _A b   ->
            n' `seq` (go _A || if x == x' then freeIn (V x n')  b else go  b)
          where
            n' = n + 1
        Pi  x' _A _B  ->
            n' `seq` (go _A || if x == x' then freeIn (V x n') _B else go _B)
          where
            n' = n + 1
        Var v'       -> v == v'
        App f a      -> go f || go a
        Const _      -> False
        NatLit _     -> False
        Nat          -> False
        FromNat      -> False
        ToNat        -> False
        ListLit t xs -> go t || any go xs
        List         -> False
        FromList     -> False
        ToList       -> False
        -- The Morte compiler enforces that all embedded values
        -- are closed expressions
        Embed _     -> False

{-| Reduce an expression to its normal form, performing both beta reduction and
    eta reduction

    `normalize` does not type-check the expression.  You may want to type-check
    expressions before normalizing them since normalization can convert an
    ill-typed expression into a well-typed expression.
-}
normalize :: Expr a -> Expr a
normalize e = case e of
    Lam x _A b   -> case b' of
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
    Pi  x _A _B  -> Pi x (normalize _A) (normalize _B)
    App f a      -> case normalize f of
        Lam x _A b     -> normalize (shift (-1) x b')  -- Beta reduce
          where
            a' = shift 1 x (normalize a)
            b' = subst x 0 a' b
        FromNat        -> case whnf a of
            NatLit n -> case fromNat n of
                Just e1 -> e1 -- Already normalized
                Nothing -> App FromNat (normalize a)
            _        -> App FromNat (normalize a)
        ToNat          -> case toNat a' of
            Just n  -> NatLit n
            Nothing -> App ToNat a'
          where
            a' = normalize a
        App FromList t -> case whnf a of
            ListLit t' xs -> fromList (normalize t', map normalize xs)
            _             -> App (App FromList (normalize t)) (normalize a)
        App ToList   t -> case Morte.Core.toList a' of
            Just (t', xs) -> ListLit t' xs
            Nothing       -> App (App ToList (normalize t)) a'
          where
            a' = normalize a
        f'         -> App f' (normalize a)
    Var   _      -> e
    Const _      -> e
    NatLit _     -> e
    Nat          -> e
    FromNat      -> FromNat
    ToNat        -> ToNat
    ListLit a xs -> ListLit (normalize a) (map normalize xs)
    List         -> List
    FromList     -> FromList
    ToList       -> ToList
    Embed p      -> Embed p

lookup :: Expr a -> Context b -> Maybe b
lookup k c = case normalize k of
    Var (V x n) -> Context.lookup x n c
    _           -> Nothing

data NatCtx = NatCtxNat | NatCtxSucc | NatCtxZero | NatCtxPred deriving (Eq)

-- | Type of a church-encoded number
natType :: Expr a
natType =
    Pi "Nat" (Const Star)
        (Pi "Succ" (Pi "pred" "Nat" "Nat") (Pi "Zero" "Nat" "Nat"))

-- | Convert a church-encoded number back into a numeric literal
toNat :: Expr a -> Maybe Int
toNat
    (Lam nat0 (Const Star)
        (Lam succ0 (Pi pred0 nat1 nat2)
            (Lam zero0 nat3 e0) ) )
    | lookup nat1 c1  == Just NatCtxNat &&
      lookup nat2 c1a == Just NatCtxNat &&
      lookup nat3 c2  == Just NatCtxNat = go e0 0
    | otherwise                         = Nothing
  where
    c0  = Context.empty
    c1  = Context.insert nat0  NatCtxNat  c0
    c1a = Context.insert pred0 NatCtxPred c1
    c2  = Context.insert succ0 NatCtxSucc c1
    c3  = Context.insert zero0 NatCtxZero c2

    go (App succ e) !m
        | lookup succ c3 == Just NatCtxSucc = go e (m + 1)
        | otherwise                         = Nothing
    go  zero        !m
        | lookup zero c3 == Just NatCtxZero = Just m
        | otherwise                         = Nothing
-- `fromNat 1` will eta-reduce to `\(Nat : *) -> \(Succ : Nat -> Nat) -> Succ
-- so we need this code to handle that special case
toNat (Lam nat0 (Const Star) (Lam succ0 (Pi _ nat1 nat2) succ1))
    | lookup nat1  c1 == Just NatCtxNat  &&
      lookup nat2  c1 == Just NatCtxNat  &&
      lookup succ1 c2 == Just NatCtxSucc = Just 1
    | otherwise                          = Nothing
  where
    c0 = Context.empty
    c1 = Context.insert nat0  NatCtxNat  c0
    c2 = Context.insert succ0 NatCtxSucc c1
toNat _ = Nothing

-- | Convert a numeric literal into a Church-encoded number
fromNat :: Int -> Maybe (Expr a)
fromNat n0
    | n0 < 0    = Nothing
    | otherwise =
        Just
            (Lam "Nat" (Const Star)
                (Lam "Succ" (Pi "pred" "Nat" "Nat")
                    (Lam "Zero" "Nat" (go n0)) ) )
  where
    go !n | n <= 0    = "Zero"
          | otherwise = App "Succ" (go (n - 1))

data ListCtx
    = ListCtxList
    | ListCtxCons
    | ListCtxNil
    | ListCtxHead
    | ListCtxTail
    deriving (Eq)

-- | The type of a Church-encoded list
listType :: Expr a -> Expr a
listType a =
    Pi "List" (Const Star)
        (Pi "Cons" (Pi "head" a' (Pi "tail" "List" "List"))
            (Pi "Nil" "List" "List") )
  where
    a' = shift 1 "List" a

-- | Convert a Church-encoded list into a list literal
toList :: Expr a -> Maybe (Expr a, [Expr a])
toList
    (Lam list0 (Const Star)
        (Lam cons0 (Pi head0 a0 (Pi tail0 list1 list2))
            (Lam nil0 list3 e0) ) )
    | lookup list1 c1a == Just ListCtxList &&
      lookup list2 c1b == Just ListCtxList &&
      lookup list3 c2  == Just ListCtxList = go e0 id
    | otherwise                            = Nothing
  where
    c0  = Context.empty
    c1  = Context.insert list0 ListCtxList c0
    c1a = Context.insert head0 ListCtxHead c1
    c1b = Context.insert tail0 ListCtxTail c1a
    c2  = Context.insert cons0 ListCtxCons c1
    c3  = Context.insert nil0  ListCtxNil  c2

    a0' = shift (-1) list0 a0

    go (App (App cons1 x) e) diffXs
        | lookup cons1 c3 == Just ListCtxCons = go e (diffXs . (x':))
        | otherwise                           = Nothing
      where
        x' = (shift (-1) list0 . shift (-1) cons0 . shift (-1) nil0) x
    go  nil1                 diffXs
        | lookup nil1  c3 == Just ListCtxNil  = Just (a0', diffXs [])
        | otherwise                           = Nothing
toList
    (Lam list0 (Const Star)
        (Lam cons0 (Pi head0 a0 (Pi tail0 list1 list2))
            (App cons1 x) ) )
    | lookup list1 c1a == Just ListCtxList &&
      lookup list2 c1b == Just ListCtxList &&
      lookup cons1 c2  == Just ListCtxCons = Just (a0', [x'])
    | otherwise                            = Nothing
 where
    c0  = Context.empty
    c1  = Context.insert list0 ListCtxList c0
    c1a = Context.insert head0 ListCtxHead c1
    c1b = Context.insert tail0 ListCtxTail c1a
    c2  = Context.insert cons0 ListCtxCons c1

    a0' = shift (-1) list0 a0

    x' = (shift (-1) list0 . shift (-1) cons0) x
toList _ = Nothing

-- TODO: Change this `"List"` variable name to not conflict with reserved
-- keyword
-- | Convert a list literal into a Church-encoded list
fromList :: (Expr a, [Expr a]) -> Expr a
fromList (a, xs) =
    Lam "List" (Const Star)
        (Lam "Cons" (Pi "head" a' (Pi "tail" "List" "List"))
            (Lam "Nil" "List" (foldr cons nil xs)) )
  where
    a' = shift 1 "List" a

    cons x = App (App "Cons" x')
      where
        x' = (shift 1 "List" . shift 1 "Cons" . shift 1 "Nil") x
    nil       = "Nil"

-- | Pretty-print a value
pretty :: Buildable a => a -> Text
pretty = Builder.toLazyText . build
