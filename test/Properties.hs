{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}

module Main (
    main
  ) where

import Control.Exception (throwIO)
import ClosedWellTyped (ClosedWellTyped(..))
import Data.Text.Lazy (Text)
import Morte.Core (Expr, X)
import NeatInterpolation (text)
import Test.Tasty (TestTree)

import qualified Data.Text.Lazy        as Text
import qualified Morte.Core            as Morte
import qualified Morte.Import          as Morte
import qualified Morte.Parser          as Morte
import qualified Test.Tasty            as Tasty
import qualified Test.Tasty.QuickCheck as QuickCheck
import qualified Test.Tasty.HUnit      as HUnit

main :: IO ()
main = Tasty.defaultMain tests

tests :: TestTree
tests =
    Tasty.testGroup "Tests"
        [ Tasty.testGroup "Properties"
            [ QuickCheck.testProperty "Normalization is idempotent"
                normalizationIsIdempotent 
            , QuickCheck.testProperty "Normalization preserves type safety"
                normalizationPreservesTypeSafety
            ]
        , Tasty.testGroup "Unit tests"
            [ HUnit.testCase "Tutorial - Identity"           example0
            , HUnit.testCase "Tutorial - id.mt"              example1
            , HUnit.testCase "Tutorial - id2.mt"             example2
            , HUnit.testCase "Tutorial - bool.mt"            example3
            , HUnit.testCase "Tutorial - pair.mt"            example4
            , HUnit.testCase "Tutorial - all.mt"             example5
            , HUnit.testCase "Tutorial - mapid1.mt"          example6
            , HUnit.testCase "Tutorial - mapid2.mt"          example7
            , HUnit.testCase "Tutorial - mapcomp1.mt"        example8
            , HUnit.testCase "Tutorial - mapcomp2.mt"        example9
            , HUnit.testCase "Tutorial - corecursive.mt - A" example10
            , HUnit.testCase "Tutorial - corecursive.mt - B" example11
            , HUnit.testCase "Tutorial - corecursive.mt - C" example12
            , HUnit.testCase "Tutorial - corecursive.mt - D" example13
            , HUnit.testCase "Tutorial - recursive.mt"       example14
            , HUnit.testCase "Tutorial - corecursive.mt"     example15
            ]
        ]

typeChecks :: Expr X -> Bool
typeChecks expr = case Morte.typeOf expr of
    Right _ -> True
    Left  _ -> False

-- Carefully note that `ClosedWellTyped` generates well-typed expressions, so
-- this is really testing that `typeChecks expr ==> typeChecks (normalize expr)`
normalizationPreservesTypeSafety :: ClosedWellTyped -> Bool
normalizationPreservesTypeSafety (ClosedWellTyped expr) =
    typeChecks (Morte.normalize expr)

-- Carefully note that `(==)` also normalizes both sides before checking for
-- α-equality, so this is really testing that `normalize (normalize expr)` and
-- `normalize expr` are α-equivalent.
normalizationIsIdempotent :: ClosedWellTyped -> Bool
normalizationIsIdempotent (ClosedWellTyped expr) = Morte.normalize expr == expr

example
    :: Text
    -> Text
    -> Text
    -> IO ()
example stdin stderr stdout =
    case Morte.exprFromText stdin of
        Left  e    -> throwIO e
        Right expr -> do
            expr' <- Morte.load expr
            case Morte.typeOf expr' of
                Left  e        -> throwIO e
                Right typeExpr -> do
                    let stderr' = Morte.pretty (Morte.normalize typeExpr)
                    let stdout' = Morte.pretty (Morte.normalize expr')
                    HUnit.assertEqual "" stderr stderr'
                    HUnit.assertEqual "" stdout stdout'

example0 :: IO ()
example0 =
    example
        "\\(a : *) -> \\(x : a) -> x"
        "∀(a : *) → ∀(x : a) → a"
        "λ(a : *) → λ(x : a) → x"

example1 :: IO ()
example1 =
    example
        (Text.fromStrict [text|
-- id.mt

-- Morte accepts comments

-- Also, whitespace is not significant
\(String : *) ->
    (\(a : *) -> \(x : a) -> x) String
|])
        "∀(String : *) → ∀(x : String) → String"
        "λ(String : *) → λ(x : String) → x"

example2 :: IO ()
example2 =
    example
        (Text.fromStrict [text|
-- id2.mt

(   \(id : forall (a : *) -> a -> a)
->  id (forall (a : *) -> a -> a) id  -- Apply the identity function to itself
)

-- id
(\(a : *) -> \(x : a) -> x)
|])
        "∀(a : *) → a → a"
        "λ(a : *) → λ(x : a) → x"

example3 :: IO ()
example3 =
    example
        (Text.fromStrict [text|
-- bool.mt

-- let data Bool = True | False
--
-- in  if True then One else Zero

(   \(Bool : *)
->  \(True  : Bool)
->  \(False : Bool)
->  \(if : Bool -> forall (r : *) -> r -> r -> r)
->  \(Int  : *)
->  \(Zero : Int)
 -> \(One  : Int)
->  if True Int One Zero
)

-- Bool
(forall (r : *) -> r -> r -> r)

-- True
(\(r : *) -> \(x : r) -> \(_ : r) -> x)

-- False
(\(r : *) -> \(_ : r) -> \(x : r) -> x)

-- if
(\(b : forall (r : *) -> r -> r -> r) -> b)
|])
    "∀(Int : *) → ∀(Zero : Int) → ∀(One : Int) → Int"
    "λ(Int : *) → λ(Zero : Int) → λ(One : Int) → One"

example4 :: IO ()
example4 =
    example
        (Text.fromStrict [text|
-- pair.mt

-- let Pair a b = P a b
--
-- in  \x y -> snd (P x y)

(   \(Pair : * -> * -> *)
->  \(P    : forall (a : *) -> forall (b : *) -> a -> b -> Pair a b)
->  \(fst  : forall (a : *) -> forall (b : *) -> Pair a b -> a)
->  \(snd  : forall (a : *) -> forall (b : *) -> Pair a b -> b)
->  \(a : *) -> \(x : a) -> \(y : a) -> snd a a (P a a x y)
)

-- Pair
(\(a : *) -> \(b : *) -> forall (r : *) -> (a -> b -> r) -> r)

-- P
(   \(a : *)
->  \(b : *)
->  \(va : a)
->  \(vb : b)
->  \(r : *)
->  \(Pair : a -> b -> r)
->  Pair va vb
)

-- fst
(   \(a : *)
->  \(b : *)
->  \(p : forall (r : *) -> (a -> b -> r) -> r)
->  p a (\(x : a) -> \(_ : b) -> x)
)

-- snd
(   \(a : *)
->  \(b : *)
->  \(p : forall (r : *) -> (a -> b -> r) -> r)
->  p b (\(_ : a) -> \(x : b) -> x)
)
|])
    "∀(a : *) → ∀(x : a) → ∀(y : a) → a"
    "λ(a : *) → λ(x : a) → λ(y : a) → y"

example5 :: IO ()
example5 =
    example
        (Text.fromStrict [text|
-- all.mt

-- let data Bool = True | False
--
--     data List a = Cons a (List a) | Nil
--
-- in  let (&&) :: Bool -> Bool -> Bool
--         (&&) b1 b2 = if b1 then b2 else False
--
--         bools :: List Bool
--         bools = Cons True (Cons True (Cons True Nil))
--
--     in  foldr bools (&&) True

(   \(Bool : *)
->  \(True  : Bool)
->  \(False : Bool)
->  \(if : Bool -> forall (r : *) -> r -> r -> r)
->  \(List : * -> *)
->  \(Cons : forall (a : *) -> a -> List a -> List a)
->  \(Nil  : forall (a : *)                -> List a)
->  \(  foldr
    :   forall (a : *) -> List a -> forall (r : *) -> (a -> r -> r) -> r -> r
    )
->  (   \((&&) : Bool -> Bool -> Bool)
    ->  \(bools : List Bool)
    ->  foldr Bool bools Bool (&&) True
    )

    -- (&&)
    (\(x : Bool) -> \(y : Bool) -> if x Bool y False)

    -- bools
    (Cons Bool True (Cons Bool True (Cons Bool True (Nil Bool))))
)

-- Bool
(forall (r : *) -> r -> r -> r)

-- True
(\(r : *) -> \(x : r) -> \(_ : r) -> x)

-- False
(\(r : *) -> \(_ : r) -> \(x : r) -> x)

-- if
(\(b : forall (r : *) -> r -> r -> r) -> b)

-- List
(   \(a : *)
->  forall (list : *)
->  (a -> list -> list)  -- Cons
->  list                 -- Nil
->  list
)

-- Cons
(   \(a : *)
->  \(va  : a)
->  \(vas : forall (list : *) -> (a -> list -> list) -> list -> list)
->  \(list : *)
->  \(Cons : a -> list -> list)
->  \(Nil  : list)
->  Cons va (vas list Cons Nil)
)

-- Nil
(   \(a : *)
->  \(list : *)
->  \(Cons : a -> list -> list)
->  \(Nil  : list)
->  Nil
)

-- foldr
(   \(a : *)
->  \(vas : forall (list : *) -> (a -> list -> list) -> list -> list)
->  vas
)
|])
    "∀(r : *) → r → r → r"
    "λ(r : *) → λ(x : r) → λ(_ : r) → x"

example6 :: IO ()
example6 =
    example
        (Text.fromStrict [text|
-- mapid1.mt

(    \(List : * -> *)
->   \(map  : forall (a : *) -> forall (b : *) -> (a -> b) -> List a -> List b)
->   \(id   : forall (a : *) -> a -> a)
    ->   \(a : *) -> map a a (id a)
)

-- List
(\(a : *) -> forall (x : *) -> (a -> x -> x) -> x -> x)

-- map
(   \(a : *)
->  \(b : *)
->  \(f : a -> b)
->  \(l : forall (x : *) -> (a -> x -> x) -> x -> x)
->  \(x : *)
->  \(Cons : b -> x -> x)
->  \(Nil: x)
->  l x (\(va : a) -> \(vx : x) -> Cons (f va) vx) Nil
)

-- id
(\(a : *) -> \(va : a) -> va)
|])
    "∀(a : *) → (∀(x : *) → (a → x → x) → x → x) → ∀(x : *) → (a → x → x) → x → x"
    "λ(a : *) → λ(l : ∀(x : *) → (a → x → x) → x → x) → l"

example7 :: IO ()
example7 =
    example
        (Text.fromStrict [text|
-- mapid2.mt

(    \(List : * -> *)
->   \(map  : forall (a : *) -> forall (b : *) -> (a -> b) -> List a -> List b)
->   \(id   : forall (a : *) -> a -> a)
    ->   \(a : *) -> id (List a)
)

-- List
(\(a : *) -> forall (x : *) -> (a -> x -> x) -> x -> x)

-- map
(   \(a : *)
->  \(b : *)
->  \(f : a -> b)
->  \(l : forall (x : *) -> (a -> x -> x) -> x -> x)
->  \(x : *)
->  \(Cons : b -> x -> x)
->  \(Nil: x)
->  l x (\(va : a) -> \(vx : x) -> Cons (f va) vx) Nil
)

-- id
(\(a : *) -> \(va : a) -> va)
|])
    "∀(a : *) → (∀(x : *) → (a → x → x) → x → x) → ∀(x : *) → (a → x → x) → x → x"
    "λ(a : *) → λ(va : ∀(x : *) → (a → x → x) → x → x) → va"

example8 :: IO ()
example8 =
    example
        (Text.fromStrict [text|
-- mapcomp1.mt

-- map (f . g)

(   \(List : * -> *)
->  \(map  : forall (a : *) -> forall (b : *) -> (a -> b) -> List a -> List b)
->  \(  (.)
    :   forall (a : *)
    ->  forall (b : *)
    ->  forall (c : *)
    ->  (b -> c)
    ->  (a -> b)
    ->  (a -> c)
    )
    ->  \(a : *)
    ->  \(b : *)
    ->  \(c : *)
    ->  \(f : b -> c)
    ->  \(g : a -> b)
    ->  map a c ((.) a b c f g)
)

-- List
(\(a : *) -> forall (x : *) -> (a -> x -> x) -> x -> x)

-- map
(   \(a : *)
->  \(b : *)
->  \(f : a -> b)
->  \(l : forall (x : *) -> (a -> x -> x) -> x -> x)
->  \(x : *)
->  \(Cons : b -> x -> x)
->  \(Nil: x)
->  l x (\(va : a) -> \(vx : x) -> Cons (f va) vx) Nil
)

-- (.)
(   \(a : *)
->  \(b : *)
->  \(c : *)
->  \(f : b -> c)
->  \(g : a -> b)
->  \(va : a)
->  f (g va)
)
|])
    "∀(a : *) → ∀(b : *) → ∀(c : *) → ∀(f : b → c) → ∀(g : a → b) → (∀(x : *) → (a → x → x) → x → x) → ∀(x : *) → (c → x → x) → x → x"
    "λ(a : *) → λ(b : *) → λ(c : *) → λ(f : b → c) → λ(g : a → b) → λ(l : ∀(x : *) → (a → x → x) → x → x) → λ(x : *) → λ(Cons : c → x → x) → l x (λ(va : a) → Cons (f (g va)))"

example9 :: IO ()
example9 =
    example
        (Text.fromStrict [text|
-- mapcomp2.mt

(   \(List : * -> *)
->  \(map  : forall (a : *) -> forall (b : *) -> (a -> b) -> List a -> List b)
->  \(  (.)
    :   forall (a : *)
    ->  forall (b : *)
    ->  forall (c : *)
    ->  (b -> c)
    ->  (a -> b)
    ->  (a -> c)
    )
    ->  \(a : *)
    ->  \(b : *)
    ->  \(c : *)
    ->  \(f : b -> c)
    ->  \(g : a -> b)
    ->  (.) (List a) (List b) (List c) (map b c f) (map a b g)
)

-- List
(\(a : *) -> forall (x : *) -> (a -> x -> x) -> x -> x)

-- map
(   \(a : *)
->  \(b : *)
->  \(f : a -> b)
->  \(l : forall (x : *) -> (a -> x -> x) -> x -> x)
->  \(x : *)
->  \(Cons : b -> x -> x)
->  \(Nil: x)
->  l x (\(va : a) -> \(vx : x) -> Cons (f va) vx) Nil
)

-- (.)
(   \(a : *)
->  \(b : *)
->  \(c : *)
->  \(f : b -> c)
->  \(g : a -> b)
->  \(va : a)
->  f (g va)
)
|])
    "∀(a : *) → ∀(b : *) → ∀(c : *) → ∀(f : b → c) → ∀(g : a → b) → (∀(x : *) → (a → x → x) → x → x) → ∀(x : *) → (c → x → x) → x → x"
    "λ(a : *) → λ(b : *) → λ(c : *) → λ(f : b → c) → λ(g : a → b) → λ(va : ∀(x : *) → (a → x → x) → x → x) → λ(x : *) → λ(Cons : c → x → x) → va x (λ(va : a) → Cons (f (g va)))"

example10 :: IO ()
example10 =
    example
        (Text.fromStrict [text|
-- corecursive.mt

-- first :: (a -> b) -> (a, c) -> (b, c)
-- first f (va, vb) = (f va, vb) 
-- 
-- data Stream a = Cons (a, Stream a)
-- 
-- map :: (a -> b) -> Stream a -> Stream b
-- map f (Cons (va, s)) = Cons (first f (va, map f s))
-- 
-- -- exampleA = exampleB
-- 
-- exampleA :: Stream a -> Stream a
-- exampleA = map id
-- 
-- exampleB :: Stream a -> Stream a
-- exampleB = id
-- 
-- -- exampleC = exampleD
-- 
-- exampleC :: (b -> c) -> (a -> b) -> Stream a -> Stream c
-- exampleC f g = map (f . g)
-- 
-- exampleD :: (b -> c) -> (a -> b) -> Stream a -> Stream c
-- exampleD f g = map f . map g

(   \(id : forall (a : *) -> a -> a)
->  \(  (.)
    :   forall (a : *)
    ->  forall (b : *)
    ->  forall (c : *)
    ->  (b -> c)
    ->  (a -> b)
    ->  (a -> c)
    )
->  \(Pair : * -> * -> *)
->  \(P : forall (a : *) -> forall (b : *) -> a -> b -> Pair a b)
->  \(  first
    :   forall (a : *)
    ->  forall (b : *)
    ->  forall (c : *)
    ->  (a -> b)
    ->  Pair a c
    ->  Pair b c
    )

->  (   \(Stream : * -> *)
    ->  \(  map
        :   forall (a : *)
        ->  forall (b : *)
        ->  (a -> b)
        ->  Stream a
        ->  Stream b
        )

        -- exampleA = exampleB
    ->  (   \(exampleA : forall (a : *) -> Stream a -> Stream a)
        ->  \(exampleB : forall (a : *) -> Stream a -> Stream a)

        -- exampleC = exampleD
        ->  \(  exampleC
            :   forall (a : *)
            ->  forall (b : *)
            ->  forall (c : *)
            ->  (b -> c)
            ->  (a -> b)
            ->  Stream a
            ->  Stream c
            )

        ->  \(  exampleD
            :   forall (a : *)
            ->  forall (b : *)
            ->  forall (c : *)
            ->  (b -> c)
            ->  (a -> b)
            ->  Stream a
            ->  Stream c
            )

        -- Uncomment the example you want to test
        ->  exampleA
--      ->  exampleB
--      ->  exampleC
--      ->  exampleD
        )

        -- exampleA
        (\(a : *) -> map a a (id a))
  
        -- exampleB
        (\(a : *) -> id (Stream a))

        -- exampleC
        (   \(a : *)
        ->  \(b : *)
        ->  \(c : *)
        ->  \(f : b -> c)
        ->  \(g : a -> b)
        ->  map a c ((.) a b c f g)
        )

        --  exampleD
        (   \(a : *)
        ->  \(b : *)
        ->  \(c : *)
        ->  \(f : b -> c)
        ->  \(g : a -> b)
        ->  (.) (Stream a) (Stream b) (Stream c) (map b c f) (map a b g)
        )
    )

    -- Stream
    (   \(a : *)
    ->  forall (x : *)
    ->  (forall (s : *) -> s -> (s -> Pair a s) -> x)
    ->  x
    )

    -- map
    (   \(a : *)
    ->  \(b : *)
    ->  \(f : a -> b)
    ->  \(  st
        :   forall (x : *) -> (forall (s : *) -> s -> (s -> Pair a s) -> x) -> x
        )
    ->  \(x : *)
    ->  \(S : forall (s : *) -> s -> (s -> Pair b s) -> x)
    ->  st
        x
        (   \(s : *)
        ->  \(seed : s)
        ->  \(step : s -> Pair a s)
        ->  S
            s
            seed
            (\(seed : s) -> first a b s f (step seed))
        )
    )
)

-- id
(\(a : *) -> \(va : a) -> va)

-- (.)
(   \(a : *)
->  \(b : *)
->  \(c : *)
->  \(f : b -> c)
->  \(g : a -> b)
->  \(va : a)
->  f (g va)
)

-- Pair
(\(a : *) -> \(b : *) -> forall (x : *) -> (a -> b -> x) -> x)

-- P
(   \(a : *)
->  \(b : *)
->  \(va : a)
->  \(vb : b)
->  \(x : *)
->  \(P : a -> b -> x)
->  P va vb
)

-- first
(   \(a : *)
->  \(b : *)
->  \(c : *)
->  \(f : a -> b)
->  \(p : forall (x : *) -> (a -> c -> x) -> x)
->  \(x : *)
->  \(Pair : b -> c -> x)
->  p x (\(va : a) -> \(vc : c) -> Pair (f va) vc)
)
|])
    "∀(a : *) → (∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x"
    "λ(a : *) → λ(st : ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → st"

example11 :: IO ()
example11 =
    example
        (Text.fromStrict [text|
-- corecursive.mt

-- first :: (a -> b) -> (a, c) -> (b, c)
-- first f (va, vb) = (f va, vb) 
-- 
-- data Stream a = Cons (a, Stream a)
-- 
-- map :: (a -> b) -> Stream a -> Stream b
-- map f (Cons (va, s)) = Cons (first f (va, map f s))
-- 
-- -- exampleA = exampleB
-- 
-- exampleA :: Stream a -> Stream a
-- exampleA = map id
-- 
-- exampleB :: Stream a -> Stream a
-- exampleB = id
-- 
-- -- exampleC = exampleD
-- 
-- exampleC :: (b -> c) -> (a -> b) -> Stream a -> Stream c
-- exampleC f g = map (f . g)
-- 
-- exampleD :: (b -> c) -> (a -> b) -> Stream a -> Stream c
-- exampleD f g = map f . map g

(   \(id : forall (a : *) -> a -> a)
->  \(  (.)
    :   forall (a : *)
    ->  forall (b : *)
    ->  forall (c : *)
    ->  (b -> c)
    ->  (a -> b)
    ->  (a -> c)
    )
->  \(Pair : * -> * -> *)
->  \(P : forall (a : *) -> forall (b : *) -> a -> b -> Pair a b)
->  \(  first
    :   forall (a : *)
    ->  forall (b : *)
    ->  forall (c : *)
    ->  (a -> b)
    ->  Pair a c
    ->  Pair b c
    )

->  (   \(Stream : * -> *)
    ->  \(  map
        :   forall (a : *)
        ->  forall (b : *)
        ->  (a -> b)
        ->  Stream a
        ->  Stream b
        )

        -- exampleA = exampleB
    ->  (   \(exampleA : forall (a : *) -> Stream a -> Stream a)
        ->  \(exampleB : forall (a : *) -> Stream a -> Stream a)

        -- exampleC = exampleD
        ->  \(  exampleC
            :   forall (a : *)
            ->  forall (b : *)
            ->  forall (c : *)
            ->  (b -> c)
            ->  (a -> b)
            ->  Stream a
            ->  Stream c
            )

        ->  \(  exampleD
            :   forall (a : *)
            ->  forall (b : *)
            ->  forall (c : *)
            ->  (b -> c)
            ->  (a -> b)
            ->  Stream a
            ->  Stream c
            )

        -- Uncomment the example you want to test
--      ->  exampleA
        ->  exampleB
--      ->  exampleC
--      ->  exampleD
        )

        -- exampleA
        (\(a : *) -> map a a (id a))
  
        -- exampleB
        (\(a : *) -> id (Stream a))

        -- exampleC
        (   \(a : *)
        ->  \(b : *)
        ->  \(c : *)
        ->  \(f : b -> c)
        ->  \(g : a -> b)
        ->  map a c ((.) a b c f g)
        )

        --  exampleD
        (   \(a : *)
        ->  \(b : *)
        ->  \(c : *)
        ->  \(f : b -> c)
        ->  \(g : a -> b)
        ->  (.) (Stream a) (Stream b) (Stream c) (map b c f) (map a b g)
        )
    )

    -- Stream
    (   \(a : *)
    ->  forall (x : *)
    ->  (forall (s : *) -> s -> (s -> Pair a s) -> x)
    ->  x
    )

    -- map
    (   \(a : *)
    ->  \(b : *)
    ->  \(f : a -> b)
    ->  \(  st
        :   forall (x : *) -> (forall (s : *) -> s -> (s -> Pair a s) -> x) -> x
        )
    ->  \(x : *)
    ->  \(S : forall (s : *) -> s -> (s -> Pair b s) -> x)
    ->  st
        x
        (   \(s : *)
        ->  \(seed : s)
        ->  \(step : s -> Pair a s)
        ->  S
            s
            seed
            (\(seed : s) -> first a b s f (step seed))
        )
    )
)

-- id
(\(a : *) -> \(va : a) -> va)

-- (.)
(   \(a : *)
->  \(b : *)
->  \(c : *)
->  \(f : b -> c)
->  \(g : a -> b)
->  \(va : a)
->  f (g va)
)

-- Pair
(\(a : *) -> \(b : *) -> forall (x : *) -> (a -> b -> x) -> x)

-- P
(   \(a : *)
->  \(b : *)
->  \(va : a)
->  \(vb : b)
->  \(x : *)
->  \(P : a -> b -> x)
->  P va vb
)

-- first
(   \(a : *)
->  \(b : *)
->  \(c : *)
->  \(f : a -> b)
->  \(p : forall (x : *) -> (a -> c -> x) -> x)
->  \(x : *)
->  \(Pair : b -> c -> x)
->  p x (\(va : a) -> \(vc : c) -> Pair (f va) vc)
)
|])
    "∀(a : *) → (∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x"
    "λ(a : *) → λ(va : ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → va"

example12 :: IO ()
example12 =
    example
        (Text.fromStrict [text|
-- corecursive.mt

-- first :: (a -> b) -> (a, c) -> (b, c)
-- first f (va, vb) = (f va, vb) 
-- 
-- data Stream a = Cons (a, Stream a)
-- 
-- map :: (a -> b) -> Stream a -> Stream b
-- map f (Cons (va, s)) = Cons (first f (va, map f s))
-- 
-- -- exampleA = exampleB
-- 
-- exampleA :: Stream a -> Stream a
-- exampleA = map id
-- 
-- exampleB :: Stream a -> Stream a
-- exampleB = id
-- 
-- -- exampleC = exampleD
-- 
-- exampleC :: (b -> c) -> (a -> b) -> Stream a -> Stream c
-- exampleC f g = map (f . g)
-- 
-- exampleD :: (b -> c) -> (a -> b) -> Stream a -> Stream c
-- exampleD f g = map f . map g

(   \(id : forall (a : *) -> a -> a)
->  \(  (.)
    :   forall (a : *)
    ->  forall (b : *)
    ->  forall (c : *)
    ->  (b -> c)
    ->  (a -> b)
    ->  (a -> c)
    )
->  \(Pair : * -> * -> *)
->  \(P : forall (a : *) -> forall (b : *) -> a -> b -> Pair a b)
->  \(  first
    :   forall (a : *)
    ->  forall (b : *)
    ->  forall (c : *)
    ->  (a -> b)
    ->  Pair a c
    ->  Pair b c
    )

->  (   \(Stream : * -> *)
    ->  \(  map
        :   forall (a : *)
        ->  forall (b : *)
        ->  (a -> b)
        ->  Stream a
        ->  Stream b
        )

        -- exampleA = exampleB
    ->  (   \(exampleA : forall (a : *) -> Stream a -> Stream a)
        ->  \(exampleB : forall (a : *) -> Stream a -> Stream a)

        -- exampleC = exampleD
        ->  \(  exampleC
            :   forall (a : *)
            ->  forall (b : *)
            ->  forall (c : *)
            ->  (b -> c)
            ->  (a -> b)
            ->  Stream a
            ->  Stream c
            )

        ->  \(  exampleD
            :   forall (a : *)
            ->  forall (b : *)
            ->  forall (c : *)
            ->  (b -> c)
            ->  (a -> b)
            ->  Stream a
            ->  Stream c
            )

        -- Uncomment the example you want to test
--      ->  exampleA
--      ->  exampleB
        ->  exampleC
--      ->  exampleD
        )

        -- exampleA
        (\(a : *) -> map a a (id a))
  
        -- exampleB
        (\(a : *) -> id (Stream a))

        -- exampleC
        (   \(a : *)
        ->  \(b : *)
        ->  \(c : *)
        ->  \(f : b -> c)
        ->  \(g : a -> b)
        ->  map a c ((.) a b c f g)
        )

        --  exampleD
        (   \(a : *)
        ->  \(b : *)
        ->  \(c : *)
        ->  \(f : b -> c)
        ->  \(g : a -> b)
        ->  (.) (Stream a) (Stream b) (Stream c) (map b c f) (map a b g)
        )
    )

    -- Stream
    (   \(a : *)
    ->  forall (x : *)
    ->  (forall (s : *) -> s -> (s -> Pair a s) -> x)
    ->  x
    )

    -- map
    (   \(a : *)
    ->  \(b : *)
    ->  \(f : a -> b)
    ->  \(  st
        :   forall (x : *) -> (forall (s : *) -> s -> (s -> Pair a s) -> x) -> x
        )
    ->  \(x : *)
    ->  \(S : forall (s : *) -> s -> (s -> Pair b s) -> x)
    ->  st
        x
        (   \(s : *)
        ->  \(seed : s)
        ->  \(step : s -> Pair a s)
        ->  S
            s
            seed
            (\(seed : s) -> first a b s f (step seed))
        )
    )
)

-- id
(\(a : *) -> \(va : a) -> va)

-- (.)
(   \(a : *)
->  \(b : *)
->  \(c : *)
->  \(f : b -> c)
->  \(g : a -> b)
->  \(va : a)
->  f (g va)
)

-- Pair
(\(a : *) -> \(b : *) -> forall (x : *) -> (a -> b -> x) -> x)

-- P
(   \(a : *)
->  \(b : *)
->  \(va : a)
->  \(vb : b)
->  \(x : *)
->  \(P : a -> b -> x)
->  P va vb
)

-- first
(   \(a : *)
->  \(b : *)
->  \(c : *)
->  \(f : a -> b)
->  \(p : forall (x : *) -> (a -> c -> x) -> x)
->  \(x : *)
->  \(Pair : b -> c -> x)
->  p x (\(va : a) -> \(vc : c) -> Pair (f va) vc)
)
|])
    "∀(a : *) → ∀(b : *) → ∀(c : *) → (b → c) → (a → b) → (∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (c → s → x) → x) → x) → x"
    "λ(a : *) → λ(b : *) → λ(c : *) → λ(f : b → c) → λ(g : a → b) → λ(st : ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → λ(x : *) → λ(S : ∀(s : *) → s → (s → ∀(x : *) → (c → s → x) → x) → x) → st x (λ(s : *) → λ(seed : s) → λ(step : s → ∀(x : *) → (a → s → x) → x) → S s seed (λ(seed : s) → λ(x : *) → λ(Pair : c → s → x) → step seed x (λ(va : a) → Pair (f (g va)))))"

example13 :: IO ()
example13 =
    example
        (Text.fromStrict [text|
-- corecursive.mt

-- first :: (a -> b) -> (a, c) -> (b, c)
-- first f (va, vb) = (f va, vb) 
-- 
-- data Stream a = Cons (a, Stream a)
-- 
-- map :: (a -> b) -> Stream a -> Stream b
-- map f (Cons (va, s)) = Cons (first f (va, map f s))
-- 
-- -- exampleA = exampleB
-- 
-- exampleA :: Stream a -> Stream a
-- exampleA = map id
-- 
-- exampleB :: Stream a -> Stream a
-- exampleB = id
-- 
-- -- exampleC = exampleD
-- 
-- exampleC :: (b -> c) -> (a -> b) -> Stream a -> Stream c
-- exampleC f g = map (f . g)
-- 
-- exampleD :: (b -> c) -> (a -> b) -> Stream a -> Stream c
-- exampleD f g = map f . map g

(   \(id : forall (a : *) -> a -> a)
->  \(  (.)
    :   forall (a : *)
    ->  forall (b : *)
    ->  forall (c : *)
    ->  (b -> c)
    ->  (a -> b)
    ->  (a -> c)
    )
->  \(Pair : * -> * -> *)
->  \(P : forall (a : *) -> forall (b : *) -> a -> b -> Pair a b)
->  \(  first
    :   forall (a : *)
    ->  forall (b : *)
    ->  forall (c : *)
    ->  (a -> b)
    ->  Pair a c
    ->  Pair b c
    )

->  (   \(Stream : * -> *)
    ->  \(  map
        :   forall (a : *)
        ->  forall (b : *)
        ->  (a -> b)
        ->  Stream a
        ->  Stream b
        )

        -- exampleA = exampleB
    ->  (   \(exampleA : forall (a : *) -> Stream a -> Stream a)
        ->  \(exampleB : forall (a : *) -> Stream a -> Stream a)

        -- exampleC = exampleD
        ->  \(  exampleC
            :   forall (a : *)
            ->  forall (b : *)
            ->  forall (c : *)
            ->  (b -> c)
            ->  (a -> b)
            ->  Stream a
            ->  Stream c
            )

        ->  \(  exampleD
            :   forall (a : *)
            ->  forall (b : *)
            ->  forall (c : *)
            ->  (b -> c)
            ->  (a -> b)
            ->  Stream a
            ->  Stream c
            )

        -- Uncomment the example you want to test
--      ->  exampleA
--      ->  exampleB
--      ->  exampleC
        ->  exampleD
        )

        -- exampleA
        (\(a : *) -> map a a (id a))
  
        -- exampleB
        (\(a : *) -> id (Stream a))

        -- exampleC
        (   \(a : *)
        ->  \(b : *)
        ->  \(c : *)
        ->  \(f : b -> c)
        ->  \(g : a -> b)
        ->  map a c ((.) a b c f g)
        )

        --  exampleD
        (   \(a : *)
        ->  \(b : *)
        ->  \(c : *)
        ->  \(f : b -> c)
        ->  \(g : a -> b)
        ->  (.) (Stream a) (Stream b) (Stream c) (map b c f) (map a b g)
        )
    )

    -- Stream
    (   \(a : *)
    ->  forall (x : *)
    ->  (forall (s : *) -> s -> (s -> Pair a s) -> x)
    ->  x
    )

    -- map
    (   \(a : *)
    ->  \(b : *)
    ->  \(f : a -> b)
    ->  \(  st
        :   forall (x : *) -> (forall (s : *) -> s -> (s -> Pair a s) -> x) -> x
        )
    ->  \(x : *)
    ->  \(S : forall (s : *) -> s -> (s -> Pair b s) -> x)
    ->  st
        x
        (   \(s : *)
        ->  \(seed : s)
        ->  \(step : s -> Pair a s)
        ->  S
            s
            seed
            (\(seed : s) -> first a b s f (step seed))
        )
    )
)

-- id
(\(a : *) -> \(va : a) -> va)

-- (.)
(   \(a : *)
->  \(b : *)
->  \(c : *)
->  \(f : b -> c)
->  \(g : a -> b)
->  \(va : a)
->  f (g va)
)

-- Pair
(\(a : *) -> \(b : *) -> forall (x : *) -> (a -> b -> x) -> x)

-- P
(   \(a : *)
->  \(b : *)
->  \(va : a)
->  \(vb : b)
->  \(x : *)
->  \(P : a -> b -> x)
->  P va vb
)

-- first
(   \(a : *)
->  \(b : *)
->  \(c : *)
->  \(f : a -> b)
->  \(p : forall (x : *) -> (a -> c -> x) -> x)
->  \(x : *)
->  \(Pair : b -> c -> x)
->  p x (\(va : a) -> \(vc : c) -> Pair (f va) vc)
)
|])
    "∀(a : *) → ∀(b : *) → ∀(c : *) → (b → c) → (a → b) → (∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (c → s → x) → x) → x) → x"
    "λ(a : *) → λ(b : *) → λ(c : *) → λ(f : b → c) → λ(g : a → b) → λ(va : ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → λ(x : *) → λ(S : ∀(s : *) → s → (s → ∀(x : *) → (c → s → x) → x) → x) → va x (λ(s : *) → λ(seed : s) → λ(step : s → ∀(x : *) → (a → s → x) → x) → S s seed (λ(seed : s) → λ(x : *) → λ(Pair : c → s → x) → step seed x (λ(va : a) → Pair (f (g va)))))"

example14 :: IO ()
example14 =
    example
        (Text.fromStrict [text|
-- recursive.mt

-- The Haskell code we will translate to Morte:
--
--     import Prelude hiding (
--         (+), (*), IO, putStrLn, getLine, (>>=), (>>), return )
-- 
--     -- Simple prelude
--
--     data Nat = Succ Nat | Zero
--
--     zero :: Nat
--     zero = Zero
--
--     one :: Nat
--     one = Succ Zero
--
--     (+) :: Nat -> Nat -> Nat
--     Zero   + n = n
--     Succ m + n = m + Succ n
--
--     (*) :: Nat -> Nat -> Nat
--     Zero   * n = Zero
--     Succ m * n = n + (m * n)
--
--     foldNat :: Nat -> (a -> a) -> a -> a
--     foldNat  Zero    f x = x
--     foldNat (Succ m) f x = f (foldNat m f x)
--
--     data IO r = PutStrLn String (IO r) | GetLine (String -> IO r) | Return r
--
--     putStrLn :: String -> IO U
--     putStrLn str = PutStrLn str (Return Unit)
--
--     getLine :: IO String
--     getLine = GetLine Return
--
--     return :: a -> IO a
--     return = Return
--
--     (>>=) :: IO a -> (a -> IO b) -> IO b
--     PutStrLn str io >>= f = PutStrLn str (io >>= f)
--     GetLine k       >>= f = GetLine (\str -> k str >>= f)
--     Return r        >>= f = f r
--
--     -- Derived functions
--
--     (>>) :: IO U -> IO U -> IO U
--     m >> n = m >>= \_ -> n
--
--     two :: Nat
--     two = one + one
--
--     three :: Nat
--     three = one + one + one
--
--     four :: Nat
--     four = one + one + one + one
--
--     five :: Nat
--     five = one + one + one + one + one
--
--     six :: Nat
--     six = one + one + one + one + one + one
--
--     seven :: Nat
--     seven = one + one + one + one + one + one + one
--
--     eight :: Nat
--     eight = one + one + one + one + one + one + one + one
--
--     nine :: Nat
--     nine = one + one + one + one + one + one + one + one + one
--
--     ten :: Nat
--     ten = one + one + one + one + one + one + one + one + one + one
--
--     replicateM_ :: Nat -> IO U -> IO U
--     replicateM_ n io = foldNat n (io >>) (return Unit)
--
--     ninetynine :: Nat
--     ninetynine = nine * ten + nine
--
--     main_ :: IO U
--     main_ = getLine >>= putStrLn

-- "Free" variables
(   \(String : *   )
->  \(U : *)
->  \(Unit : U)

    -- Simple prelude
->  (   \(Nat : *)
    ->  \(zero : Nat)
    ->  \(one : Nat)
    ->  \((+) : Nat -> Nat -> Nat)
    ->  \((*) : Nat -> Nat -> Nat)
    ->  \(foldNat : Nat -> forall (a : *) -> (a -> a) -> a -> a)
    ->  \(IO : * -> *)
    ->  \(return : forall (a : *) -> a -> IO a)
    ->  \((>>=)
        :   forall (a : *)
        ->  forall (b : *)
        ->  IO a
        ->  (a -> IO b)
        ->  IO b
        )
    ->  \(putStrLn : String -> IO U)
    ->  \(getLine : IO String)

        -- Derived functions
    ->  (   \((>>) : IO U -> IO U -> IO U)
        ->  \(two   : Nat)
        ->  \(three : Nat)
        ->  \(four  : Nat)
        ->  \(five  : Nat)
        ->  \(six   : Nat)
        ->  \(seven : Nat)
        ->  \(eight : Nat)
        ->  \(nine  : Nat)
        ->  \(ten   : Nat)
        ->  (   \(replicateM_ : Nat -> IO U -> IO U)
            ->  \(ninetynine : Nat)
            ->  replicateM_ ninetynine ((>>=) String U getLine putStrLn)
            )

            -- replicateM_
            (   \(n : Nat)
            ->  \(io : IO U)
            ->  foldNat n (IO U) ((>>) io) (return U Unit)
            )

            -- ninetynine
            ((+) ((*) nine ten) nine)
        )

        -- (>>)
        (   \(m : IO U)
        ->  \(n : IO U)
        ->  (>>=) U U m (\(_ : U) -> n)
        )

        -- two
        ((+) one one)

        -- three
        ((+) one ((+) one one))

        -- four
        ((+) one ((+) one ((+) one one)))

        -- five
        ((+) one ((+) one ((+) one ((+) one one))))

        -- six
        ((+) one ((+) one ((+) one ((+) one ((+) one one)))))

        -- seven
        ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one one))))))

        -- eight
        ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one one)))))))
        -- nine
        ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one one))))))))

        -- ten
        ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one one)))))))))
    )

    -- Nat
    (   forall (a : *)
    ->  (a -> a)
    ->  a
    ->  a
    )

    -- zero
    (   \(a : *)
    ->  \(Succ : a -> a)
    ->  \(Zero : a)
    ->  Zero
    )

    -- one
    (   \(a : *)
    ->  \(Succ : a -> a)
    ->  \(Zero : a)
    ->  Succ Zero
    )

    -- (+)
    (   \(m : forall (a : *) -> (a -> a) -> a -> a)
    ->  \(n : forall (a : *) -> (a -> a) -> a -> a)
    ->  \(a : *)
    ->  \(Succ : a -> a)
    ->  \(Zero : a)
    ->  m a Succ (n a Succ Zero)
    )

    -- (*)
    (   \(m : forall (a : *) -> (a -> a) -> a -> a)
    ->  \(n : forall (a : *) -> (a -> a) -> a -> a)
    ->  \(a : *)
    ->  \(Succ : a -> a)
    ->  \(Zero : a)
    ->  m a (n a Succ) Zero
    )

    -- foldNat
    (   \(n : forall (a : *) -> (a -> a) -> a -> a)
    ->  n
    )

    -- IO
    (   \(r : *)
    ->  forall (x : *)
    ->  (String -> x -> x)
    ->  ((String -> x) -> x)
    ->  (r -> x)
    ->  x
    )

    -- return
    (   \(a : *)
    ->  \(va : a)
    ->  \(x : *)
    ->  \(PutStrLn : String -> x -> x)
    ->  \(GetLine : (String -> x) -> x)
    ->  \(Return : a -> x)
    ->  Return va
    )

    -- (>>=)
    (   \(a : *)
    ->  \(b : *)
    ->  \(m : forall (x : *)
        ->  (String -> x -> x)
        ->  ((String -> x) -> x)
        ->  (a -> x)
        ->  x
        )
    ->  \(f : a
        ->  forall (x : *)
        -> (String -> x -> x)
        -> ((String -> x) -> x)
        -> (b -> x)
        -> x
        )
    ->  \(x : *)
    ->  \(PutStrLn : String -> x -> x)
    ->  \(GetLine : (String -> x) -> x)
    ->  \(Return : b -> x)
    ->  m x PutStrLn GetLine (\(va : a) -> f va x PutStrLn GetLine Return)
    )

    -- putStrLn
    (   \(str : String)
    ->  \(x : *)
    ->  \(PutStrLn : String -> x -> x  )
    ->  \(GetLine  : (String -> x) -> x)
    ->  \(Return   : U -> x)
    ->  PutStrLn str (Return Unit)
    )

    -- getLine
    (   \(x : *)
    ->  \(PutStrLn : String -> x -> x  )
    ->  \(GetLine  : (String -> x) -> x)
    ->  \(Return   : String -> x)
    -> GetLine Return
    )
)
|])
    "∀(String : *) → ∀(U : *) → ∀(Unit : U) → ∀(x : *) → (String → x → x) → ((String → x) → x) → (U → x) → x"
    "λ(String : *) → λ(U : *) → λ(Unit : U) → λ(x : *) → λ(PutStrLn : String → x → x) → λ(GetLine : (String → x) → x) → λ(Return : U → x) → GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (GetLine (λ(va : String) → PutStrLn va (Return Unit))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"

example15 :: IO ()
example15 =
    example
        (Text.fromStrict [text|
-- corecursive.mt

-- data IOF r s = PutStrLn String s | GetLine (String -> s) | Return r
--
-- data IO r = forall s . MkIO s (s -> IOF r s)
--
-- main = MkIO Nothing (maybe (\str -> PutStrLn str Nothing) (GetLine Just))

(   \(String : *)
->  (   \(Maybe : * -> *)
    ->  \(Just : forall (a : *) -> a -> Maybe a)
    ->  \(Nothing : forall (a : *) -> Maybe a)
    ->  \(  maybe
        :   forall (a : *) -> Maybe a -> forall (x : *) -> (a -> x) -> x -> x
        )
    ->  \(IOF : * -> * -> *)
    ->  \(  PutStrLn
        :   forall (r : *)
        ->  forall (s : *)
        ->  String
        ->  s
        ->  IOF r s
        )
    ->  \(  GetLine
        :   forall (r : *)
        ->  forall (s : *)
        ->  (String -> s)
        ->  IOF r s
        )
    ->  \(  Return
        :   forall (r : *)
        ->  forall (s : *)
        ->  r
        ->  IOF r s
        )
    ->  (   \(IO : * -> *)
        ->  \(  MkIO
            :   forall (r : *) -> forall (s : *) -> s -> (s -> IOF r s) -> IO r
            )
        ->  (   \(main : forall (r : *) -> IO r)
            ->  main
            )

            -- main
            (   \(r : *)
            ->  MkIO
                r
                (Maybe String)
                (Nothing String)
                (   \(m : Maybe String)
                ->  maybe
                        String
                        m
                        (IOF r (Maybe String))
                        (\(str : String) ->
                            PutStrLn r (Maybe String) str (Nothing String)
                        )
                        (GetLine r (Maybe String) (Just String))
                )
            )
        )

        -- IO
        (   \(r : *)
        ->  forall (x : *)
        ->  (forall (s : *) -> s -> (s -> IOF r s) -> x)
        ->  x
        )

        -- MkIO
        (   \(r : *)
        ->  \(s : *)
        ->  \(seed : s)
        ->  \(step : s -> IOF r s)
        ->  \(x : *)
        ->  \(k : forall (s : *) -> s -> (s -> IOF r s) -> x)
        ->  k s seed step
        )
    )

    -- Maybe
    (\(a : *) -> forall (x : *) -> (a -> x) -> x -> x)

    -- Just
    (   \(a : *)
    ->  \(va : a)
    ->  \(x : *)
    ->  \(Just : a -> x)
    ->  \(Nothing : x)
    ->  Just va
    )

    -- Nothing
    (   \(a : *)
    ->  \(x : *)
    ->  \(Just : a -> x)
    ->  \(Nothing : x)
    ->  Nothing
    )

    -- maybe
    (\(a : *) -> \(m : forall (x : *) -> (a -> x) -> x -> x) -> m)

    -- IOF
    (   \(r : *)
    ->  \(s : *)
    ->  forall (x : *)
    ->  (String -> s -> x)
    ->  ((String -> s) -> x)
    ->  (r -> x)
    ->  x
    )

    -- PutStrLn
    (   \(r : *)
    ->  \(s : *)
    ->  \(str : String)
    ->  \(vs : s)
    ->  \(x : *)
    ->  \(PutStrLn : String -> s -> x)
    ->  \(GetLine : (String -> s) -> x)
    ->  \(Return : r -> x)
    ->  PutStrLn str vs
    )

    -- GetLine
    (   \(r : *)
    ->  \(s : *)
    ->  \(k : String -> s)
    ->  \(x : *)
    ->  \(PutStrLn : String -> s -> x)
    ->  \(GetLine : (String -> s) -> x)
    ->  \(Return : r -> x)
    ->  GetLine k
    )

    -- Return
    (   \(r : *)
    ->  \(s : *)
    ->  \(vr : r)
    ->  \(x : *)
    ->  \(PutStrLn : String -> s -> x)
    ->  \(GetLine : (String -> s) -> x)
    ->  \(Return : r -> x)
    ->  Return vr
    )

)
|])
    "∀(String : *) → ∀(r : *) → ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (String → s → x) → ((String → s) → x) → (r → x) → x) → x) → x"
    "λ(String : *) → λ(r : *) → λ(x : *) → λ(k : ∀(s : *) → s → (s → ∀(x : *) → (String → s → x) → ((String → s) → x) → (r → x) → x) → x) → k (∀(x : *) → (String → x) → x → x) (λ(x : *) → λ(Just : String → x) → λ(Nothing : x) → Nothing) (λ(m : ∀(x : *) → (String → x) → x → x) → m (∀(x : *) → (String → (∀(x : *) → (String → x) → x → x) → x) → ((String → ∀(x : *) → (String → x) → x → x) → x) → (r → x) → x) (λ(str : String) → λ(x : *) → λ(PutStrLn : String → (∀(x : *) → (String → x) → x → x) → x) → λ(GetLine : (String → ∀(x : *) → (String → x) → x → x) → x) → λ(Return : r → x) → PutStrLn str (λ(x : *) → λ(Just : String → x) → λ(Nothing : x) → Nothing)) (λ(x : *) → λ(PutStrLn : String → (∀(x : *) → (String → x) → x → x) → x) → λ(GetLine : (String → ∀(x : *) → (String → x) → x → x) → x) → λ(Return : r → x) → GetLine (λ(va : String) → λ(x : *) → λ(Just : String → x) → λ(Nothing : x) → Just va)))"
