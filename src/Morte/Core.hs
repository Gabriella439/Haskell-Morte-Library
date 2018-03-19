{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
    buildExpr,
    buildExprASCII,

    -- * Errors
    TypeError(..),
    TypeMessage(..),
    ) where

#if MIN_VERSION_base(4,8,0)
#else
import Control.Applicative (Applicative(..), (<$>))
#endif
import Control.DeepSeq (NFData(..))
import Control.Exception (Exception)
import Control.Monad (mzero)
import Data.Binary (Binary(..), Get, Put)
import Data.Foldable
import Data.Monoid ((<>))
import Data.String (IsString(..))
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder (Builder)
import Data.Traversable
import Data.Typeable (Typeable)
import Data.Word (Word8)
import Filesystem.Path.CurrentOS (FilePath)
import Formatting.Buildable (Buildable(..))
import Morte.Context (Context)
import Prelude hiding (FilePath)

import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Binary.Get                  as Get
import qualified Data.Binary.Put                  as Put
import qualified Data.Text.Encoding               as Text
import qualified Data.Text.Lazy                   as Text
import qualified Data.Text.Lazy.Builder           as Builder
import qualified Filesystem.Path.CurrentOS        as Filesystem
import qualified Morte.Context                    as Context

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
        Put.putWord64le (fromIntegral n)
    get = V <$> getUtf8 <*> fmap fromIntegral Get.getWord64le

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
    | URL  Text
    deriving (Eq, Ord, Show)

instance Buildable Path where
    build (File file)
        |  Text.isPrefixOf  "./" txt
        || Text.isPrefixOf   "/" txt
        || Text.isPrefixOf "../" txt
        = build txt <> " "
        | otherwise
        = "./" <> build txt <> " "
      where
        txt = Text.fromStrict (either id id (Filesystem.toText file))
    build (URL  str ) = build str <> " "

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
    -- | > Embed path     ~  #path
    | Embed a
    deriving (Functor, Foldable, Traversable, Show)

instance Applicative Expr where
    pure = Embed

    mf <*> mx = case mf of
        Const c     -> Const c
        Var   v     -> Var v
        Lam x _A  b -> Lam x (_A <*> mx) ( b <*> mx)
        Pi  x _A _B -> Pi  x (_A <*> mx) (_B <*> mx)
        App f a     -> App (f <*> mx) (a <*> mx)
        Embed f     -> fmap f mx

instance Monad Expr where
    return = Embed

    m >>= k = case m of
        Const c     -> Const c
        Var   v     -> Var v
        Lam x _A  b -> Lam x (_A >>= k) ( b >>= k)
        Pi  x _A _B -> Pi  x (_A >>= k) (_B >>= k)
        App f a     -> App (f >>= k) (a >>= k)
        Embed r     -> k r

match :: Text -> Int -> Text -> Int -> [(Text, Text)] -> Bool
match xL nL xR nR  []                                      = xL == xR && nL == nR
match xL 0  xR 0  ((xL', xR'):_ ) | xL == xL' && xR == xR' = True
match xL nL xR nR ((xL', xR'):xs) = nL' `seq` nR' `seq` match xL nL' xR nR' xs
  where
    nL' = if xL == xL' then nL - 1 else nL
    nR' = if xR == xR' then nR - 1 else nR

instance Eq a => Eq (Expr a) where
    eL0 == eR0 = State.evalState (go (normalize eL0) (normalize eR0)) []
      where
--      go :: Expr a -> Expr a -> State [(Text, Text)] Bool
        go (Const cL) (Const cR) = return (cL == cR)
        go (Var (V xL nL)) (Var (V xR nR)) = do
            ctx <- State.get
            return (match xL nL xR nR ctx)
        go (Lam xL tL bL) (Lam xR tR bR) = do
            ctx <- State.get
            eq1 <- go tL tR
            if eq1
                then do
                    State.put ((xL, xR):ctx)
                    eq2 <- go bL bR
                    State.put ctx
                    return eq2
                else return False
        go (Pi xL tL bL) (Pi xR tR bR) = do
            ctx <- State.get
            eq1 <- go tL tR
            if eq1
                then do
                    State.put ((xL, xR):ctx)
                    eq2 <- go bL bR
                    State.put ctx
                    return eq2
                else return False
        go (App fL aL) (App fR aR) = do
            b1 <- go fL fR
            if b1 then go aL aR else return False
        go (Embed pL) (Embed pR) = return (pL == pR)
        go _ _ = return False

instance Binary a => Binary (Expr a) where
    put e = case e of
        Const c     -> do
            put (0 :: Word8)
            put c
        Var x       -> do
            put (1 :: Word8)
            put x
        Lam x _A b  -> do
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
        Embed p     -> do
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
            5 -> Embed <$> get
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
        Embed p     -> rnf p

buildLabel :: Text -> Builder
buildLabel = build

buildNumber :: Int -> Builder
buildNumber = build

buildConst :: Const -> Builder
buildConst = build

buildVExpr :: Var -> Builder
buildVExpr (V a 0) = buildLabel a
buildVExpr (V a b) = buildLabel a <> "@" <> buildNumber b

-- | Pretty-print an expression as a `Builder`, using Unicode symbols
buildExpr :: Buildable a => Expr a -> Builder
buildExpr (Lam a b c) =
    "λ(" <> buildLabel a <> " : " <> buildExpr b <> ") → " <> buildExpr c
buildExpr (Pi "_" b c) =
    buildBExpr b <> " → " <> buildExpr c
buildExpr (Pi a b c) =
    "∀(" <> buildLabel a <> " : " <> buildExpr b <> ") → " <> buildExpr c
buildExpr e =
    buildBExpr e

buildBExpr :: Buildable a => Expr a -> Builder
buildBExpr (App a b) = buildBExpr a <> " " <> buildAExpr b
buildBExpr  a        = buildAExpr a

buildAExpr :: Buildable a => Expr a -> Builder
buildAExpr (Var   a) = buildVExpr a
buildAExpr (Const a) = buildConst a
buildAExpr (Embed a) = build a
buildAExpr  a        = "(" <> buildExpr a <> ")"

-- | Pretty-print an expression as a `Builder`, using ASCII symbols
buildExprASCII :: Buildable a => Expr a -> Builder
buildExprASCII (Lam a b c) =
    "\\(" <> buildLabel a <> " : " <> buildExprASCII b <> ") -> " <> buildExprASCII c
buildExprASCII (Pi "_" b c) =
    buildBExprASCII b <> " -> " <> buildExprASCII c
buildExprASCII (Pi a b c) =
    "forall (" <> buildLabel a <> " : " <> buildExprASCII b <> ") -> " <> buildExprASCII c
buildExprASCII e =
    buildBExprASCII e

buildBExprASCII :: Buildable a => Expr a -> Builder
buildBExprASCII (App a b) = buildBExprASCII a <> " " <> buildAExprASCII b
buildBExprASCII  a        = buildAExprASCII a

buildAExprASCII :: Buildable a => Expr a -> Builder
buildAExprASCII (Var   a) = buildVExpr a
buildAExprASCII (Const a) = buildConst a
buildAExprASCII (Embed a) = build a
buildAExprASCII  a        = "(" <> buildExprASCII a <> ")"

-- | Generates a syntactically valid Morte program
instance Buildable a => Buildable (Expr a)
  where
    build = buildExpr

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
    show = Text.unpack . pretty

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
        Lam x _A  b -> Lam x (go _A c) (go  b $! c')
          where
            c' = if x == x0 then c + 1 else c
        Pi  x _A _B -> Pi  x (go _A c) (go _B $! c')
          where
            c' = if x == x0 then c + 1 else c
        App f a     -> App (go f c) (go a c)
        Var (V x n) -> n' `seq` Var (V x n')
          where
            n' = if x == x0 && n >= c then n + d else n
        Const k     -> Const k
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
    Const c     -> fmap Const (axiom c)
    Var (V x n) -> case Context.lookup x n ctx of
        Nothing -> Left (TypeError ctx e UnboundVariable)
        Just a  -> return a
    Lam x _A b  -> do
        _ <- typeWith ctx _A
        let ctx' = fmap (shift 1 x) (Context.insert x _A ctx)
        _B <- typeWith ctx' b
        let p = Pi x _A _B
        _t <- typeWith ctx p
        return p
    Pi  x _A _B -> do
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
    Embed p     -> absurd p

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
        f'         -> App f' a
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
    Lam x _A b -> case b' of
        App f a -> case a' of
            Var v' | v == v' && not (v `freeIn` f) ->
                shift (-1) x f  -- Eta reduce
                   | otherwise                     ->
                e'
              where
                v = V x 0
            _                                      -> e'
          where
            a' = whnf a
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
    Embed p    -> Embed p

-- | Pretty-print a value
pretty :: Buildable a => a -> Text
pretty = Builder.toLazyText . build
