{-| Morte is a minimalist implementation of the calculus of constructions that
    comes with a parser, type-checker, optimizer, and pretty-printer.

    You can think of Morte as a very low-level virtual machine for functional
    languages.  This virtual machine was designed with the following design
    principles, in descending order of importance:

    * Be super-optimizable - by disabling unrestricted recursion

    * Be portable - so you can transmit code between different languages

    * Be efficient - so that Morte can scale to large code bases

    * Be simple - so people can reason about Morte's soundness


    This library does not provide any front-end or back-end language for Morte.
    These will be provided as separate libraries in the future.

    The \"Introduction\" section walks through basic usage of the compiler and
    library.

    The \"Desugaring\" section explains how to desugar complex abstractions to
    Morte's core calculus.

    The \"Optimization\" section explains how Morte optimizes programs,
    providing several long-form example programs and their optimized output.
-}

module Morte.Tutorial (
    -- * Introduction
    -- $introduction

    -- * Desugaring
    -- $desugaring

    -- ** Let
    -- $let

    -- ** Simple types
    -- $types

    -- ** Newtypes
    -- $newtypes

    -- ** Recursion
    -- $recursion

    -- ** Existential Quantification
    -- $existential

    -- ** Corecursion
    -- $corecursion

    -- * Optimization
    -- $optimization

    -- ** Normalization
    -- $normalization

    -- * Effects
    -- $effects

    -- * Portability
    -- $portability
    ) where

import Morte.Core

{- $introduction
    You can test out your first Morte program using the @morte@ executable
    provided by this library.  This executable reads a Morte program from
    @stdin@, outputs the type of the program to @stderr@, and outputs the
    optimized program to @stdout@.

    We'll begin by translating Haskell's identity function to Morte.  For
    reference, `id` is defined in Haskell as:

> id :: a -> a
> id x = x

    We will enter the equivalent Morte program at the command line:

> $ morte
> \(a : *) -> \(x : a) -> x <Enter>
> <Ctrl-D>
> ∀(a : *) → a → a
> λ(a : *) → λ(x : a) → x
> $

    The compiler outputs two lines.  The first line is the type, which is output
    to @stderr@.  The second line is the optimized program, which is output to
    @stdout@.

    Compare the type output by the compiler with the equivalent Haskell type:

> -- Haskell
> id :: a -> a
>
> -- Morte
> ∀(a : *) → a → a

    The first thing you'll notice is that Morte explicitly quantifies all types.
    In Haskell, you can do this, too, using the @ExplicitForAll@ extension:

> id :: forall a . a -> a

    The Morte compiler uses a Unicode forall symbol to sweeten the output, but
    Morte also accepts other equivalents, too, such as:

> -- Ascii '∀'
> \/(a : *) -> a -> a
>
> -- English
> forall (a : *) -> a -> a
>
> -- Unicode Capital Pi
> Π(a : *) -> a -> a
>
> -- ASCII 'Π'
> |~|(a : *) -> a -> a

    Also, Morte accepts both Unicode and ASCII arrow symbols.

    The compiler's last output line is the optimized program, which in this case
    is identical to our original program (except sweetened with Unicode).
    Compare to the equivalent Haskell code:

> -- Haskell code, desugared to a lambda expression
> id = \x -> x
>
> λ(a : *) → λ(x : a) → x

    Notice that Morte explicitly binds the type @\'a\'@ as an additional
    parameter.  We use this to assign a type to the bound variable @x@.  In
    Morte, all bound variables must be explicitly annotated with a type because
    Morte does not perform any type inference.

    Now let's modify our program to accept an external type, such as @String@
    and then we can specialize our identity function to that type.  Remember
    that the type is just another argument to our function, so we specialize
    our identity function by just applying it to @String@.

    We'll use a file this time instead of entering the program at the command
    line:

> -- id.mt
>
> -- Morte accepts comments
>
> -- Also, whitespace is not significant
> \(String : *) ->
>     (\(a : *) -> \(x : a) -> x) String

    Then we'll type-check and optimize this program:

> $ morte < id.mt
> ∀(String : *) → String → String
> λ(String : *) → λ(x : String) → x

    Morte optimizes our program to the identity function on @String@s, but if
    you notice carefully this is indistinguishable from our original identity
    function because we still take the @String@ type as parameter.  The only
    difference is that we've renamed @\'a\'@ to @String@.

    In fact, Morte knows this and can detect when two expressions are equal
    up to renaming of bound variables (a.k.a. \"alpha-equivalence\").  The
    compiler does not support testing programs for equality, but the library
    does:
   
> $ ghci
> Prelude> import Morte.Core
> Prelude Morte.Core> :set -XOverloadedStrings
> Prelude Morte.Core> let id = Lam "a" (Const Star) (Lam "x" "a" "x")
> Prelude Morte.Core> let id' = Lam "String" (Const Star) (App id "String")
> Prelude Morte.Core> id == id'
> True

    In fact, Morte's equality operator also detects \"beta-equivalence\" and
    \"eta-equivalence\", too, which you can think of as equivalence of normal
    forms.

    We can even use this equality operator to prove the equivalence of many (but
    not all) complex programs, but first we need to learn how to define more
    complex abstractions using Morte's restrictive language, as outlined in the
    next section.
-}

{- $desugaring
    The `Expr` type defines Morte's syntax, which is very simple:

> data Expr
>     = Const Const        -- Type system constants
>     | Var Var            -- Bound variables
>     | Lam Var Expr Expr  -- Lambda
>     | Pi  Var Expr Expr  -- "forall"
>     | App Expr Expr      -- Function application

    For example, you can see what @id'@ from the previous section expands out to
    by using the `Show` instance for `Expr`:
    
> Lam (V "String" 0) (Const Star) (
>     App (Lam (V "a" 0) (Const Star) (
>              Lam (V "x" 0) (Var (V "a" 0)) (Var (V "x" 0))))
>         (Var (V "String" 0)))

    ... although Morte provides syntactic sugar for building expressions by
    hand using the `OverloadedStrings` instance, so you could instead write:

> Lam "String" (Const Star) (
>     App (Lam "a" (Const Star)( Lam "x" "a" "a")) "String" )

    Note that Morte's syntax does not include:

    * @let@ expressions

    * @case@ expressions

    * Built-in values other than functions

    * Built-in types other than function types

    * @newtype@s

    * Support for multiple expressions/statements

    * Modules or imports

    * Recursion / Corecursion


    Future front-ends to Morte will support these higher-level abstractions, but
    for now you must desugar all of these to lambda calculus before Morte can
    type-check and optimize your program.  The following sections explain how to
    desugar these abstractions from a Haskell-like language.
-}

{- $let
    Given a non-recursive @let@ statement of the form:

> let var1 :: type1
>     var1 = expr1
>
>     var2 :: type2
>     var2 = expr2
>
>     ...
>
>     varN :: typeN
>     varN = exprN
>
> in  result

    You can desugar that to:

> (\(var1 : type1) -> \(var2 : type2) -> ... -> \(varN : typeN) -> result) expr1 expr2 ... exprN

    Remember that whitespace is not significant, so you can also write that as:

> (   \(var1 : type1)
> ->  \(var2 : type2)
> ->  ...
> ->  \(varN : typeN)
> ->  result
> )
> expr1
> expr2
> ...
> exprN

    The Morte compiler does not mistake @expr1@ through @exprN@ for additional
    top-level expresions, because a Morte program only consists of a single
    expression.

    Carefully note that the following expression:

> let var1 : type1
>     var1 = expr1
>
>     var2 : type2
>     var2 = type2
>
> in  result

    ... is not the same as:

> let var1 : type1
>     var1 = expr1
>
> in  let var2 : type2
>         var2 = expr2
>
>     in  result

    They desugar to different Morte code and sometimes the distinction between
    the two is significant.

    Using @let@, you can desugar this:

> let id : forall (a : *) -> a -> a
>     id = \(a : *) -> \(x : *) -> x
>
> in  id (forall (a : *) -> a -> a) id

    ... into this:

> -- id2.mt
>
> (   \(id : forall (a : *) -> a -> a)
> ->  id (forall (a : *) -> a -> a) id  -- Apply the identity function to itself
> )
> 
> -- id
> (\(a : *) -> \(x : a) -> x)

    ... and the compiler will type-check and optimize that to:

> $ morte < id2.mt
> ∀(a : *) → a → a
> λ(a : *) → λ(x : a) → x

-}

{- $types
    The following sections use a technique known as Boehm-Berarducci encoding to
    convert recursive data types to lambda terms.  If you already know what
    Boehm-Berarducci encoding is then you can skip these sections.  You might
    already recognize this technique by the names of overlapping techniques such
    as CPS-encoding, Church-encoding, or F-algebras.

    I'll first explain how to desugar a somewhat complicated non-recursive type
    and then show how this trick specializes to simpler types.  The first
    example is quite long, but you'll see that it gets much more compact in the
    simpler examples.

    Given the following non-recursive type:

> let data T a b c = A | B a | C b c
>
> in  result

    You can desugar that to the following Morte code:

>     -- The type constructor
> (   \(T : * -> * -> * -> *)
>
>     -- The value constructors
> ->  \(A : forall (a : *) -> forall (b : *) -> forall (c : *)           -> T a b c)
> ->  \(B : forall (a : *) -> forall (b : *) -> forall (c : *) -> a      -> T a b c)
> ->  \(C : forall (a : *) -> forall (b : *) -> forall (c : *) -> b -> c -> T a b c)
>
>     -- Pattern match on T
> ->  \(  matchT
>     :   forall (a : *) -> forall (b : *) -> forall (c : *)
>     ->  T a b c
>     ->  forall (r : *)
>     ->  r              -- `A` branch of the pattern match
>     ->  (a -> r)       -- `B` branch of the pattern match
>     ->  (b -> c -> r)  -- `C` branch of the pattern match
>     ->  r
>     )
> -> result
> )
>
> -- A value of type `T a b c` is just a preformed pattern match
> (   \(a : *) -> \(b : *) -> \(c : *)
> ->  forall (r : *)
> ->  r              -- A branch of the pattern match
> ->  (a -> r)       -- B branch of the pattern match
> ->  (b -> c -> r)  -- C branch of the pattern match
> ->  r
> )
>
> -- Constructor for A
> (   \(a : *)
> ->  \(b : *)
> ->  \(c : *)
> ->  \(r : *)
> ->  \(A : r)
> ->  \(B : a -> r)
> ->  \(C : b -> c -> r)
> ->  A
> )
>
> -- Constructor for B
> (   \(a : *)
> ->  \(b : *)
> ->  \(c : *)
> ->  \(va : a)
> ->  \(r : *)
> ->  \(A : r)
> ->  \(B : a -> r)
> ->  \(C : b -> c -> r)
> ->  B va
> )
>
> -- Constructor for C
> (   \(a : *)
> ->  \(b : *)
> ->  \(c : *)
> ->  \(vb : b)
> ->  \(vc : c)
> ->  \(r : *)
> ->  \(A : r)
> ->  \(B : a -> r)
> ->  \(C : b -> c -> r)
> ->  C vb vc
> )
>
> -- matchT is just the identity function
> (   \(a : *)
> ->  \(b : *)
> ->  \(c : *)
> ->  \(t : forall (r : *) -> r -> (a -> r) -> (b -> c -> r) -> r)
> ->  t
> )

    Within the @result@ expression, you could assemble values of type @\'T\'@
    using the constructors:

> Context:
> String : *
> Int    : *
> Bool   : *
> s      : String
> i      : Int
> b      : Bool
>
> A String Int Bool     : T String Int Bool
> B String Int Bool s   : T String Int Bool
> C String Int Bool i b : T String Int Bool

    ... and you could pattern match on any value of type @\'T\'@ using @matchT@:

> Context:
> String : *
> Int    : *
> Bool   : *
> r      : *  -- The result type of all three case branches
> t      : T String Int Bool
>
> matchT String Int Bool r t
>     (                                ...)  -- Branch if you match `A`
>     (\(s : String) ->                ...)  -- Branch if you match `B`
>     (\(i : Int   ) -> \(b : Bool) -> ...)  -- Branch if you match `C`

    Now let's see how this specializes to a simpler example: Haskell's `Bool`
    type.

> -- let data Bool = True | False
> --
> -- in  result
>
> (   \(Bool : *)
> ->  \(True  : Bool)
> ->  \(False : Bool)
> ->  \(if : Bool -> forall (r : *) -> r -> r -> r)
> ->  result
> )
> 
> -- Bool
> (forall (r : *) -> r -> r -> r)
> 
> -- True
> (\(r : *) -> \(x : r) -> \(_ : r) -> x)
> 
> -- False
> (\(r : *) -> \(_ : r) -> \(x : r) -> x)
> 
> -- if
> (\(b : forall (r : *) -> r -> r -> r) -> b)

    Notice that @if@ is our function to pattern match on a `Bool`.  The two
    branches of the @if@ correspond to the @then@ and @else@ clauses.

    Using this definition of `Bool` we can define a simple program:

> -- bool.mt
>
> -- let data Bool = True | False
> --
> -- in  if True then One else Zero
>
> (   \(Bool : *)
> ->  \(True  : Bool)
> ->  \(False : Bool)
> ->  \(if : Bool -> forall (r : *) -> r -> r -> r)
> ->  \(Int  : *)
> ->  \(Zero : Int)
>  -> \(One  : Int)
> ->  if True Int One Zero
> )
> 
> -- Bool
> (forall (r : *) -> r -> r -> r)
> 
> -- True
> (\(r : *) -> \(x : r) -> \(_ : r) -> x)
> 
> -- False
> (\(r : *) -> \(_ : r) -> \(x : r) -> x)
> 
> -- if
> (\(b : forall (r : *) -> r -> r -> r) -> b)

   If you type-check and optimize this, you get:

> $ morte < bool.mt
> ∀(Int : *) → Int → Int → Int
> λ(Int : *) → λ(Zero : Int) → λ(One : Int) → One

    The compiler reduces the program to @One@.  All the dead code has been
    eliminated.  Also, if you study the output program closely, you'll notice
    that it's equivalent to @False@ and the program's type is equivalent to the
    @Bool@ type.  Try flipping the @Zero@ and @One@ arguments to @if@ and see
    what happens.

    Now let's implement Haskell's binary tuple type, except using a named type
    and constructor since Morte does not support tuple syntax:

> -- let Pair a b = P a b
> --
> -- in  result
>
> (   \(Pair : * -> * -> *)
> ->  \(P    : forall (a : *) -> forall (b : *) -> a -> b -> Pair a b)
> ->  \(fst  : forall (a : *) -> forall (b : *) -> Pair a b -> a)
> ->  \(snd  : forall (a : *) -> forall (b : *) -> Pair a b -> b)
> ->  result
> )
> 
> -- Pair
> (\(a : *) -> \(b : *) -> forall (r : *) -> (a -> b -> r) -> r)
> 
> -- P
> (   \(a : *)
> ->  \(b : *)
> ->  \(va : a)
> ->  \(vb : b)
> ->  \(r : *)
> ->  \(Pair : a -> b -> r)
> ->  Pair va vb
> )
> 
> -- fst
> (   \(a : *)
> ->  \(b : *)
> ->  \(p : forall (r : *) -> (a -> b -> r) -> r)
> ->  p a (\(x : a) -> \(_ : b) -> x)
> )
> 
> -- snd
> (   \(a : *)
> ->  \(b : *)
> ->  \(p : forall (r : *) -> (a -> b -> r) -> r)
> ->  p b (\(_ : a) -> \(x : b) -> x)
> )

    Here we provide @fst@ and @snd@ functions instead of `matchPair`.

    Let's write a simple program that uses this @Pair@ type:

> -- pair.mt
>
> -- let Pair a b = P a b
> --
> -- in  \x y -> snd (P x y)
>
> (   \(Pair : * -> * -> *)
> ->  \(P    : forall (a : *) -> forall (b : *) -> a -> b -> Pair a b)
> ->  \(fst  : forall (a : *) -> forall (b : *) -> Pair a b -> a)
> ->  \(snd  : forall (a : *) -> forall (b : *) -> Pair a b -> b)
> ->  \(a : *) -> \(x : a) -> \(y : a) -> snd a a (P a a x y)
> )
>
> -- Pair
> (\(a : *) -> \(b : *) -> forall (r : *) -> (a -> b -> r) -> r)
>
> -- P
> (   \(a : *)
> ->  \(b : *)
> ->  \(va : a)
> ->  \(vb : b)
> ->  \(r : *)
> ->  \(Pair : a -> b -> r)
> ->  Pair va vb
> )
> 
> -- fst
> (   \(a : *)
> ->  \(b : *)
> ->  \(p : forall (r : *) -> (a -> b -> r) -> r)
> ->  p a (\(x : a) -> \(_ : b) -> x)
> )
> 
> -- snd
> (   \(a : *)
> ->  \(b : *)
> ->  \(p : forall (r : *) -> (a -> b -> r) -> r)
> ->  p b (\(_ : a) -> \(x : b) -> x)
> )

    If you compile and type-check that you get:

> $ morte < pair.mt
> ∀(a : *) → a → a → a
> λ(a : *) → λ(x : a) → λ(y : a) → y

    This is also equal to our previous program.  Just rename @\'a\'@ to @Int@,
    rename @\'x\'@ to @Zero@ and rename @\'y\'@ to @One@.

    You can also import data types from whatever backend you use by accepting
    those types and functions on those types as explicit arguments to your
    program.  For example, if you want to use machine integers and machine
    arithmetic, then you can just parametrize your program on the integer type
    and operations on that type:

>     \(Int    : *)
> ->  \((+)    : Int -> Int -> Int)
> ->  \((*)    : Int -> Int -> Int)
>     ...

    However, the more types and operations you encode natively within Morte the
    more the optimizer can simplify your program.  This is because there is no
    runtime performance penalty from using natively encoded data types.  Morte
    will optimize these all away at compile time because they are just ordinary
    functions under the hood and Morte optimizes away all function calls.
-}

{- $newtypes
   Defining a newtype is no different than defining a data type with a single
   constructor with one field:

> -- let newtype Name = MkName { getName :: String }
> --
> -- in  result
>
> (   \(Name    : *)
> ->  \(MkName  : String -> Name  )
> ->  \(getName : Name   -> String)
> ->  result
> )
>
> -- Name
> String
> 
> -- MkName
> (\(str : String) -> str)
>
> -- getName
> (\(str : String) -> str)

    Within the expression @result@, @Name@ is actually a new type, meaning that
    a value of type @Name@ will not type-check as a @String@ and, vice versa, a
    value of type @String@ will not type-check as a @Name@.  You would have to
    explicitly convert back and forth between @Name@ and @String@ using the
    @MkName@ and @getName@ functions.

    We can prove this using the following example program:

> -- newtype.mt
>
> -- let newtype Name = MkName { getName :: String }
> --
> -- in  (f :: Name -> Name) (x :: String)
> 
> (   \(Name    : *)
> ->  \(MkName  : String -> Name  )
> ->  \(getName : Name   -> String)
> ->  \(f : Name -> Name) -> \(x : String) -> f x
> )
> 
> -- Name
> String
> 
> -- MkName
> (\(str : String) -> str)
> 
> -- getName
> (\(str : String) -> str)

    That programs fails to type-check, giving the following error message:

> $ morte < newtype.mt
> Context:
> Name : *
> MkName : String → Name
> getName : Name → String
> f : Name → Name
> x : String
> 
> Expression: f x
> 
> Error: Function applied to argument of the wrong type
> 
> Expected type: Name
> Argument type: String

    There is never a performance penalty for using newtypes, but this is just a
    special case of the fact that there is no performance penalty for using any
    natively encoded data types in Morte.
-}

{- $recursion
    Defining a recursive data type is very similar to defining a non-recursive
    type.  Let's use lists as an example:

> let data List a = Cons a (List a) | Nil
>
> in  result

    The equivalent Morte code is:

> -- let data List a = Cons a (List a) | Nil
> --
> -- in  result
> 
> (   \(List : * -> *)
> ->  \(Cons : forall (a : *) -> a -> List a -> List a)
> ->  \(Nil  : forall (a : *)                -> List a)
> ->  \(  foldr
>     :   forall (a : *) -> List a -> forall (r : *) -> (a -> r -> r) -> r -> r
>     )
> ->  result
> )
> 
> -- List
> (   \(a : *)
> ->  forall (list : *)
> ->  (a -> list -> list)  -- Cons
> ->  list                 -- Nil
> ->  list
> )
> 
> -- Cons
> (   \(a : *)
> ->  \(va  : a)
> ->  \(vas : forall (list : *) -> (a -> list -> list) -> list -> list)
> ->  \(list : *)
> ->  \(Cons : a -> list -> list)
> ->  \(Nil  : list)
> ->  Cons va (vas list Cons Nil)
> )
> 
> -- Nil
> (   \(a : *)
> ->  \(list : *)
> ->  \(Cons : a -> list -> list)
> ->  \(Nil  : list)
> ->  Nil
> )
> 
> -- foldr
> (   \(a : *)
> ->  \(vas : forall (list : *) -> (a -> list -> list) -> list -> list)
> ->  vas
> )

    Here I use the @list@ type variable where previous examples would use
    @\'r\'@ to emphasize that the continuations that a @List@ consumes both have
    the same shape as the list constructors.  You just replace all recursive
    references to the data type with the type of the final result, pretending
    that the final result is a list.

    Let's extend the @List@ example with the @Bool@ code to implement Haskell's
    @any@ function and use it on an actual @List@ of @Bool@s:

> -- any.mt
>
> -- let data Bool = True | False
> --
> --     data List a = Cons a (List a) | Nil
> --
> -- in  let (&&) :: Bool -> Bool -> Bool
> --         (&&) b1 b2 = if b1 then b2 else False
> --
> --         bools :: List Bool
> --         bools = Cons True (Cons True (Cons True Nil))
> --
> --     in  foldr bools (&&) True
> 
> (   \(Bool : *)
> ->  \(True  : Bool)
> ->  \(False : Bool)
> ->  \(if : Bool -> forall (r : *) -> r -> r -> r)
> ->  \(List : * -> *)
> ->  \(Cons : forall (a : *) -> a -> List a -> List a)
> ->  \(Nil  : forall (a : *)                -> List a)
> ->  \(  foldr
>     :   forall (a : *) -> List a -> forall (r : *) -> (a -> r -> r) -> r -> r
>     )
> ->  (   \((&&) : Bool -> Bool -> Bool)
>     ->  \(bools : List Bool)
>     ->  foldr Bool bools Bool (&&) True
>     )
> 
>     -- (&&)
>     (\(b@1 : Bool) -> \(b@2 : Bool) -> if b@1 Bool b@2 False)
> 
>     -- bools
>     (Cons Bool True (Cons Bool True (Cons Bool True (Nil Bool))))
> )
> 
> -- Bool
> (forall (r : *) -> r -> r -> r)
> 
> -- True
> (\(r : *) -> \(x : r) -> \(_ : r) -> x)
> 
> -- False
> (\(r : *) -> \(_ : r) -> \(x : r) -> x)
> 
> -- if
> (\(b : forall (r : *) -> r -> r -> r) -> b)
> 
> -- List
> (   \(a : *)
> ->  forall (list : *)
> ->  (a -> list -> list)  -- Cons
> ->  list                 -- Nil
> ->  list
> )
> 
> -- Cons
> (   \(a : *)
> ->  \(va  : a)
> ->  \(vas : forall (list : *) -> (a -> list -> list) -> list -> list)
> ->  \(list : *)
> ->  \(Cons : a -> list -> list)
> ->  \(Nil  : list)
> ->  Cons va (vas list Cons Nil)
> )
> 
> -- Nil
> (   \(a : *)
> ->  \(list : *)
> ->  \(Cons : a -> list -> list)
> ->  \(Nil  : list)
> ->  Nil
> )
> 
> -- foldr
> (   \(a : *)
> ->  \(vas : forall (list : *) -> (a -> list -> list) -> list -> list)
> ->  vas
> )

    If you type-check and optimize the program, the compiler will statically
    evaluate the entire computation, reducing the program to @True@:

> $ morte < any.mt
> ∀(r : *) → r → r → r
> λ(r : *) → λ(x : r) → λ(_ : r) → x

    Here's another example of encoding a recursive type, using natural numbers:

> -- let data Nat = Succ Nat | Zero
> --
> -- in  result
> 
> (   \(Nat : *)
> ->  \(Succ : Nat -> Nat)
> ->  \(Zero : Nat)
> ->  \(foldNat : Nat -> forall (r : *) -> (r -> r) -> r -> r)
> ->  result
> )
> 
> -- Nat
> (   forall (nat : *)
> ->  (nat -> nat)  -- Succ
> ->  nat           -- Zero
> ->  nat
> )
> 
> (   \(n : forall (nat : *) -> (nat -> nat) -> nat -> nat)
> ->  \(nat : *)
> ->  \(Succ : nat -> nat)
> ->  \(Zero : nat)
> ->  Succ (n nat Succ Zero)
> )
> 
> (   \(nat : *)
> ->  \(Succ : nat -> nat)
> ->  \(Zero : nat)
> ->  Zero
> )
> 
> (   \(n : forall (nat : *) -> (nat -> nat) -> nat -> nat)
> ->  n
> )

    As an exercise, try implementing @(+)@ for the @Nat@ type, then implementing
    Haskell's @sum@, then using @sum@ on a @List@ of @Nat@s.  Verify that the
    compiler statically computes the sum as a Church-encoded numeral.
     
    The encoding outlined in this section is equivalent to an F-algebra encoding
    of a recursive type, which is any encoding of the following shape:

> forall (x : *) -> (F x -> x) -> x

    .. where @F@ is a strictly-positive functor.

    Our @List a@ encoding is isomorphic to an F-algebra encoding where:

> F x = Maybe (a, x)

    ... and our @Nat@ encoding is isomorphic to an F-algebra encoding where:

> F x = Maybe x

-}

{- $existential
    You can translate existential quantified types to use universal
    quantification.  For example, consider the following existentially
    quantified Haskell type:

> let data Example = forall s . MkExample s (s -> String)
>
> in  result

    The equivalent Morte program is:

> -- let data Example = forall s . Example s (s -> String)
> --
> -- in  result
> 
> \(String : *) ->
> (   \(Example : *)
> ->  \(MkExample : forall (s : *) -> s -> (s -> String) -> Example)
> ->  \(  matchExample
>     :   Example
>     ->  forall (x : *)
>     ->  (forall (s : *) -> s -> (s -> String) -> x)
>     ->  x
>     )
> ->  result
> )
> 
> -- Example
> (   forall (x : *)
> ->  (forall (s : *) -> s -> (s -> String) -> x)  -- MkExample
> ->  x
> )
> 
> -- MkExample
> (   \(s : *)
> ->  \(vs : s)
> ->  \(fs : s -> String)
> ->  \(x : *)
> ->  \(MkExample : forall (s : *) -> s -> (s -> String) -> x)
> ->  MkExample s vs fs
> )
> 
> -- matchExample
> (   \(e : forall (x : *) -> (forall (s : *) -> s -> (s -> String) -> x) -> x)
> ->  e
> )

    More generally, for every constructor that you existentially quantify with a
    type variable @\'s\'@ you just add a @(forall (s : *) -> ...)@ prefix to
    that constructor's continuation.  If you \"pattern match\" against the
    constructor corresponding to that continuation you will bind the
    existentially quantified type.

    For example, we can pattern match against the @MkExample@ constructor like
    this:

> \(e : Example) -> matchExample e
>       (\(s : *) -> (x : s) -> (f : s -> String) -> expr) 

    The type @\'s\'@ will be in scope for @expr@ and we can safely apply the
    bound function to the bound value if we so chose to extract a @String@,
    despite not knowing which type @\'s\'@ we bound:

> \(e : Example) -> matchExample e
>       (\(s : *) -> (x : s) -> (f : s -> String) -> f x) 

    The two universal quantifiers in the definition of the @Example@ type
    statically forbid the type @\'s\'@ from leaking from the pattern match.
-}

{- $corecursion
    Recursive types can only encode finite data types.  If you want a
    potentially infinite data type (such as an infinite list), you must encode
    the type in a different way.

    For example, consider the following infinite stream type:

> codata Stream a = Cons a (Stream a)

    If you tried to encode that as a recursive type, you would end up with this
    Morte type:

> \(a : *) -> forall (x : *) -> (a -> x -> x) -> x

    However, this type is uninhabited, meaning that you cannot create a value of
    the above type for any choice of @\'a\'@.  Try it, if you don't believe
    me.

    Potentially infinite types must be encoded using a dual trick, where we
    store them as an existentially quantified seed and a generating step
    function that emits one layer alongside a new seed.

    For example, the above @Stream@ type would translate to the following
    non-recursive representation.  The @StreamF@ constructor represents one
    layer and the @Stream@ type lets us generate an infinite number of layers
    by providing an initial seed of type @s@ and a generation function of type
    @(s -> StreamF a s)@:

> -- Replace the corecursive occurrence of `Stream` with `s`
> data StreamF a s = Cons a s
>
> data Stream a = forall s . MkStream s (s -> StreamF a s)

    The above type will work for any type @\'s\'@ as the @\'s\'@ is
    existentially quantified.  The end user of the @Stream@ will never be able
    to detect what the original type of @s@ was, because the @MkStream@
    constructor closes over that information permanently.

    An example @Stream@ is the following lazy stream of natural numbers:

> nats :: Stream Int
> nats = MkStream 0 (\n -> Cons n (n + 1))

    Internally, the above @Stream@ uses an @Int@ as its internal state, but
    that is completely invisible to all downstream code, which cannot access
    the concrete type of the internal state any longer.

    In fact, this trick of using a seed and a generating step function is a
    special case of a F-coalgebra encoding of a corecursive type, which is
    anything of the form:

> exists s . (s, s -> F s)

    Once you F-coalgebra encode the @Stream@ type you can translate the type to
    Morte using the rules for existential quantification given in the previous
    section:

> (forall (x : *) -> (forall (s : *) -> s -> (s -> StreamF a s) -> x) -> x

    See the next section for some example @Stream@ code.
-}

{- $optimization
    You might wonder why Morte forbids recursion, forcing us to encode data
    types F-algebras or F-coalgebras.  Morte imposes this restriction this in
    order to super-optimize your program.  For example, consider the following
    program which maps the identity function over a list:

> -- mapid1.mt
>
> (    \(List : * -> *)
> ->   \(map  : forall (a : *) -> forall (b : *) -> (a -> b) -> List a -> List b)
> ->   \(id   : forall (a : *) -> a -> a)
>     ->   \(a : *) -> map a a (id a)
> )
> 
> -- List
> (\(a : *) -> forall (x : *) -> (a -> x -> x) -> x -> x)
> 
> -- map
> (   \(a : *)
> ->  \(b : *)
> ->  \(f : a -> b)
> ->  \(l : forall (x : *) -> (a -> x -> x) -> x -> x)
> ->  \(x : *)
> ->  \(Cons : b -> x -> x)
> ->  \(Nil: x)
> ->  l x (\(va : a) -> \(vx : x) -> Cons (f va) vx) Nil
> )
> 
> -- id
> (\(a : *) -> \(va : a) -> va)

    If we examine the compiler output, we'll see that the compiler fuses away
    the @map@, leaving behind the identity function on lists:

> $ morte < mapid1.mt
> ∀(a : *) → (∀(x : *) → (a → x → x) → x → x) → ∀(x : *) → (a → x → x) → x → x
> λ(a : *) → λ(l : ∀(x : *) → (a → x → x) → x → x) → l

    We can prove this by replacing our @map@ with the identity function on
    lists:

> -- mapid2.mt
>
> (    \(List : * -> *)
> ->   \(map  : forall (a : *) -> forall (b : *) -> (a -> b) -> List a -> List b)
> ->   \(id   : forall (a : *) -> a -> a)
>     ->   \(a : *) -> id (List a)
> )
> 
> -- List
> (\(a : *) -> forall (x : *) -> (a -> x -> x) -> x -> x)
> 
> -- map
> (   \(a : *)
> ->  \(b : *)
> ->  \(f : a -> b)
> ->  \(l : forall (x : *) -> (a -> x -> x) -> x -> x)
> ->  \(x : *)
> ->  \(Cons : b -> x -> x)
> ->  \(Nil: x)
> ->  l x (\(va : a) -> \(vx : x) -> Cons (f va) vx) Nil
> )
> 
> -- id
> (\(a : *) -> \(va : a) -> va)

    The compiler output for this is alpha-equivalent:

> $ morte < mapid2.mt
> ∀(a : *) → (∀(x : *) → (a → x → x) → x → x) → ∀(x : *) → (a → x → x) → x → x
> λ(a : *) → λ(va : ∀(x : *) → (a → x → x) → x → x) → va

    However, we don't have to trust our fallible eyes.  We can enlist the
    @morte@ library to mechanically check that the two programs are equal:

> $ ghci
> Prelude> import qualified Data.Text.Lazy.IO as Text
> Prelude Text> txt1 <- Text.readFile "mapid1.mt"
> Prelude Text> txt2 <- Text.readFile "mapid2.mt"
> Prelude Text> import Morte.Parser
> Prelude Text Morte.Parser> let e1 = exprFromText txt1
> Prelude Text Morte.Parser> let e2 = exprFromText txt2
> Prelude Text Morte.Parser> import Control.Applicative
> Prelude Text Morte.Parser Control.Applicative> liftA2 (==) e1 e2
> Right True

    We just mechanically proved that @map id == id@.  When we transform our code
    to a non-recursive form we've done most of the work.  The compiler can then
    check that the two programs are equal by just optimizing both programs and
    verifying that they produce identical optimized code.

    Using this same trick we can also prove the other map fusion law:

> map (f . g) = map f . map g

    Here is the first program, corresponding to the left-hand side of the
    equation:

> -- mapcomp1.mt
>
> -- map (f . g)
> 
> (   \(List : * -> *)
> ->  \(map  : forall (a : *) -> forall (b : *) -> (a -> b) -> List a -> List b)
> ->  \(  (.)
>     :   forall (a : *)
>     ->  forall (b : *)
>     ->  forall (c : *)
>     ->  (b -> c)
>     ->  (a -> b)
>     ->  (a -> c)
>     )
>     ->  \(a : *)
>     ->  \(b : *)
>     ->  \(c : *)
>     ->  \(f : b -> c)
>     ->  \(g : a -> b)
>     ->  map a c ((.) a b c f g)
> )
> 
> -- List
> (\(a : *) -> forall (x : *) -> (a -> x -> x) -> x -> x)
> 
> -- map
> (   \(a : *)
> ->  \(b : *)
> ->  \(f : a -> b)
> ->  \(l : forall (x : *) -> (a -> x -> x) -> x -> x)
> ->  \(x : *)
> ->  \(Cons : b -> x -> x)
> ->  \(Nil: x)
> ->  l x (\(va : a) -> \(vx : x) -> Cons (f va) vx) Nil
> )
> 
> -- (.)
> (   \(a : *)
> ->  \(b : *)
> ->  \(c : *)
> ->  \(f : b -> c)
> ->  \(g : a -> b)
> ->  \(va : a)
> ->  f (g va)
> )

    ... and here is the second program, corresponding to the right-hand side:

> -- mapcomp2.mt
> 
> (   \(List : * -> *)
> ->  \(map  : forall (a : *) -> forall (b : *) -> (a -> b) -> List a -> List b)
> ->  \(  (.)
>     :   forall (a : *)
>     ->  forall (b : *)
>     ->  forall (c : *)
>     ->  (b -> c)
>     ->  (a -> b)
>     ->  (a -> c)
>     )
>     ->  \(a : *)
>     ->  \(b : *)
>     ->  \(c : *)
>     ->  \(f : b -> c)
>     ->  \(g : a -> b)
>     ->  (.) (List a) (List b) (List c) (map b c f) (map a b g)
> )
> 
> -- List
> (\(a : *) -> forall (x : *) -> (a -> x -> x) -> x -> x)
> 
> -- map
> (   \(a : *)
> ->  \(b : *)
> ->  \(f : a -> b)
> ->  \(l : forall (x : *) -> (a -> x -> x) -> x -> x)
> ->  \(x : *)
> ->  \(Cons : b -> x -> x)
> ->  \(Nil: x)
> ->  l x (\(va : a) -> \(vx : x) -> Cons (f va) vx) Nil
> )
> 
> -- (.)
> (   \(a : *)
> ->  \(b : *)
> ->  \(c : *)
> ->  \(f : b -> c)
> ->  \(g : a -> b)
> ->  \(va : a)
> ->  f (g va)
> )

    Verify using the @morte@ library that those produce identical expressions.
    For reference, they both generate the following type and optimized program
    that loops over the list just once, applying @\'f\'@ and @\'g\'@ to every
    value:

> $ morte < mapcomp1.mt
> ∀(a : *) → ∀(b : *) → ∀(c : *) → (b → c) → (a → b) → (∀(x : *) → (a → x → x) →
>  x → x) → ∀(x : *) → (c → x → x) → x → x
> λ(a : *) → λ(b : *) → λ(c : *) → λ(f : b → c) → λ(g : a → b) → λ(l : ∀(x : *) 
> → (a → x → x) → x → x) → λ(x : *) → λ(Cons : c → x → x) → l x (λ(va : a) → Con
> s (f (g va)))

    We can also prove @map@ fusion for corecursive streams as well.  Just use
    the following program:

> -- first :: (a -> b) -> (a, c) -> (b, c)
> -- first f (va, vb) = (f va, vb) 
> -- 
> -- data Stream a = Cons (a, Stream a)
> -- 
> -- map :: (a -> b) -> Stream a -> Stream b
> -- map f (Cons (va, s)) = Cons (first f (va, map f s))
> -- 
> -- -- example1 = example2
> -- 
> -- example1 :: Stream a -> Stream a
> -- example1 = map id
> -- 
> -- example2 :: Stream a -> Stream a
> -- example2 = id
> -- 
> -- -- example3 = example4
> -- 
> -- example3 :: (b -> c) -> (a -> b) -> Stream a -> Stream c
> -- example3 f g = map (f . g)
> -- 
> -- example4 :: (b -> c) -> (a -> b) -> Stream a -> Stream c
> -- example4 f g = map f . map g
> 
> (   \(id : forall (a : *) -> a -> a)
> ->  \(  (.)
>     :   forall (a : *)
>     ->  forall (b : *)
>     ->  forall (c : *)
>     ->  (b -> c)
>     ->  (a -> b)
>     ->  (a -> c)
>     )
> ->  \(Pair : * -> * -> *)
> ->  \(P : forall (a : *) -> forall (b : *) -> a -> b -> Pair a b)
> ->  \(  first
>     :   forall (a : *)
>     ->  forall (b : *)
>     ->  forall (c : *)
>     ->  (a -> b)
>     ->  Pair a c
>     ->  Pair b c
>     )
> 
> ->  (   \(Stream : * -> *)
>     ->  \(  map
>         :   forall (a : *)
>         ->  forall (b : *)
>         ->  (a -> b)
>         ->  Stream a
>         ->  Stream b
>         )
> 
>         -- example@1 = example@2
>     ->  (   \(example@1 : forall (a : *) -> Stream a -> Stream a)
>         ->  \(example@2 : forall (a : *) -> Stream a -> Stream a)
> 
>         -- example@3 = example@4
>         ->  \(  example@3
>             :   forall (a : *)
>             ->  forall (b : *)
>             ->  forall (c : *)
>             ->  (b -> c)
>             ->  (a -> b)
>             ->  Stream a
>             ->  Stream c
>             )
> 
>         ->  \(  example@4
>             :   forall (a : *)
>             ->  forall (b : *)
>             ->  forall (c : *)
>             ->  (b -> c)
>             ->  (a -> b)
>             ->  Stream a
>             ->  Stream c
>             )
> 
>         -- Uncomment the example you want to test
>         ->  example@1
> --      ->  example@2
> --      ->  example@3
> --      ->  example@4
>         )
> 
>         -- example@1
>         (\(a : *) -> map a a (id a))
>   
>         -- example@2
>         (\(a : *) -> id (Stream a))
> 
>         -- example@3
>         (   \(a : *)
>         ->  \(b : *)
>         ->  \(c : *)
>         ->  \(f : b -> c)
>         ->  \(g : a -> b)
>         ->  map a c ((.) a b c f g)
>         )
> 
>         --  example@4
>         (   \(a : *)
>         ->  \(b : *)
>         ->  \(c : *)
>         ->  \(f : b -> c)
>         ->  \(g : a -> b)
>         ->  (.) (Stream a) (Stream b) (Stream c) (map b c f) (map a b g)
>         )
>     )
> 
>     -- Stream
>     (   \(a : *)
>     ->  forall (x : *)
>     ->  (forall (s : *) -> s -> (s -> Pair a s) -> x)
>     ->  x
>     )
> 
>     -- map
>     (   \(a : *)
>     ->  \(b : *)
>     ->  \(f : a -> b)
>     ->  \(  st
>         :   forall (x : *) -> (forall (s : *) -> s -> (s -> Pair a s) -> x) -> x
>         )
>     ->  \(x : *)
>     ->  \(S : forall (s : *) -> s -> (s -> Pair b s) -> x)
>     ->  st
>         x
>         (   \(s : *)
>         ->  \(seed : s)
>         ->  \(step : s -> Pair a s)
>         ->  S
>             s
>             seed
>             (\(seed@1 : s) -> first a b s f (step seed@1))
>         )
>     )
> )
> 
> -- id
> (\(a : *) -> \(va : a) -> va)
> 
> -- (.)
> (   \(a : *)
> ->  \(b : *)
> ->  \(c : *)
> ->  \(f : b -> c)
> ->  \(g : a -> b)
> ->  \(va : a)
> ->  f (g va)
> )
> 
> -- Pair
> (\(a : *) -> \(b : *) -> forall (x : *) -> (a -> b -> x) -> x)
> 
> -- P
> (   \(a : *)
> ->  \(b : *)
> ->  \(va : a)
> ->  \(vb : b)
> ->  \(x : *)
> ->  \(P : a -> b -> x)
> ->  P va vb
> )
> 
> -- first
> (   \(a : *)
> ->  \(b : *)
> ->  \(c : *)
> ->  \(f : a -> b)
> ->  \(p : forall (x : *) -> (a -> c -> x) -> x)
> ->  \(x : *)
> ->  \(Pair : b -> c -> x)
> ->  p x (\(va : a) -> \(vc : c) -> Pair (f va) vc)
> )
> 

Both @example\@1@ and @example\@2@ generate identical optimized expressions,
corresponding to the identity function on @Stream@:

> $ morte < corecursive.mt
> ∀(a : *) → (∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) →
> x) → ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x
> λ(a : *) → λ(st : ∀(x : *) → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) 
> → x) → x) → st

Similarly, both @example\@3@ and @example\@4@ generate identical optimized
expressions, corresponding to applying @f@ and @g@ to every value emitted by
the generating step function:

> $ morte < corecursive.mt
> ∀(a : *) → ∀(b : *) → ∀(c : *) → (b → c) → (a → b) → (∀(x : *) → (∀(s : *) → s
>  → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → ∀(x : *) → (∀(s : *) → s → (s 
> → ∀(x : *) → (c → s → x) → x) → x) → x
> λ(a : *) → λ(b : *) → λ(c : *) → λ(f : b → c) → λ(g : a → b) → λ(st : ∀(x : *)
>  → (∀(s : *) → s → (s → ∀(x : *) → (a → s → x) → x) → x) → x) → λ(x : *) → λ(S
>  : ∀(s : *) → s → (s → ∀(x : *) → (c → s → x) → x) → x) → st x (λ(s : *) → λ(s
> eed : s) → λ(step : s → ∀(x : *) → (a → s → x) → x) → S s seed (λ(seed@1 : s) 
> → λ(x : *) → λ(Pair : c → s → x) → step seed@1 x (λ(va : a) → Pair (f (g va)))
> ))

-}

{- $normalization
    Morte has a very simple optimization scheme.  The only thing that Morte does
    to optimize programs is beta-reduce them and eta-reduce them to their
    normal form.  Since Morte's core calculus is non-recursive, this reduction
    is guaranteed to terminate.

    The way Morte compares expressions for equality is just to compare their
    normal forms.  Note that this definition of equality does not detect all
    equal programs.  Here's an example of an equality that Morte does not
    currently detect (but might detect in the future):

> \(k : forall (x : *) -> a -> x) -> k (f . g)
>
> = f (k g)

    This is an example of a free theorem: an equality that can be deduced purely
    from the type of @k@.  Morte may eventually use free theorems to further
    normalize expression, but for now it does not.

    Normalization leads to certain emergent properties when optimizing recursive
    code or corecursive code.  If you optimize a corecursive loop you will
    produce code equivalent an @while@ loop where the seed is the initial state
    of the loop and the generating step function unfolds one iteration of the
    loop.  If you optimize a recursive loop you will generate an unrolled loop.
    See the next section for an example of Morte generating a very large
    unrolled loop.

    Normalization confers one very useful property: the runtime performance of a
    Morte program is completely impervious to abstraction.  Adding additional
    abstraction layers may increase compile time, but runtime performance will
    remain constant.  The runtime performance of a program is solely a function
    of the program's normal form, and adding additional abstraction layers never
    changes the normal form your program.
-}

{- $effects
    Morte uses the Haskell approach to effects, where effects are represented as
    terms within the language and evaluation order has no impact on order of
    effects.  This is by necessity: if evaluation triggered side effects then
    Morte would be unable to optimize expressions by normalizing them.

    The following example encodes @IO@ within Morte as an abstract syntax tree
    of effects (a.k.a. a "free monad").  Encoding @IO@ as a free monad is not
    strictly necessary, but doing so makes Morte aware of the monad laws, which
    allows it to greatly simplify the program:

> -- The Haskell code we will translate to Morte:
> --
> --     import Prelude hiding (
> --         (+), (*), IO, putStrLn, getLine, (>>=), (>>), return )
> -- 
> --     -- Simple prelude
> --
> --     data Nat = Succ Nat | Zero
> --
> --     zero :: Nat
> --     zero = Zero
> --
> --     one :: Nat
> --     one = Succ Zero
> --
> --     (+) :: Nat -> Nat -> Nat
> --     Zero   + n = n
> --     Succ m + n = m + Succ n
> --
> --     (*) :: Nat -> Nat -> Nat
> --     Zero   * n = Zero
> --     Succ m * n = n + (m * n)
> --
> --     foldNat :: Nat -> (a -> a) -> a -> a
> --     foldNat  Zero    f x = x
> --     foldNat (Succ m) f x = f (foldNat m f x)
> --
> --     data IO r = PutStrLn String (IO r) | GetLine (String -> IO r) | Return r
> --
> --     putStrLn :: String -> IO U
> --     putStrLn str = PutStrLn str (Return Unit)
> --
> --     getLine :: IO String
> --     getLine = GetLine Return
> --
> --     return :: a -> IO a
> --     return = Return
> --
> --     (>>=) :: IO a -> (a -> IO b) -> IO b
> --     PutStrLn str io >>= f = PutStrLn str (io >>= f)
> --     GetLine k       >>= f = GetLine (\str -> k str >>= f)
> --     Return r        >>= f = f r
> --
> --     -- Derived functions
> --
> --     (>>) :: IO U -> IO U -> IO U
> --     m >> n = m >>= \_ -> n
> --
> --     two :: Nat
> --     two = one + one
> --
> --     three :: Nat
> --     three = one + one + one
> --
> --     four :: Nat
> --     four = one + one + one + one
> --
> --     five :: Nat
> --     five = one + one + one + one + one
> --
> --     six :: Nat
> --     six = one + one + one + one + one + one
> --
> --     seven :: Nat
> --     seven = one + one + one + one + one + one + one
> --
> --     eight :: Nat
> --     eight = one + one + one + one + one + one + one + one
> --
> --     nine :: Nat
> --     nine = one + one + one + one + one + one + one + one + one
> --
> --     ten :: Nat
> --     ten = one + one + one + one + one + one + one + one + one + one
> --
> --     replicateM_ :: Nat -> IO U -> IO U
> --     replicateM_ n io = foldNat n (io >>) (return Unit)
> --
> --     ninetynine :: Nat
> --     ninetynine = nine * ten + nine
> --
> --     main_ :: IO U
> --     main_ = getLine >>= putStrLn
> 
> -- "Free" variables
> (   \(String : *   )
> ->  \(U : *)
> ->  \(Unit : U)
> 
>     -- Simple prelude
> ->  (   \(Nat : *)
>     ->  \(zero : Nat)
>     ->  \(one : Nat)
>     ->  \((+) : Nat -> Nat -> Nat)
>     ->  \((*) : Nat -> Nat -> Nat)
>     ->  \(foldNat : Nat -> forall (a : *) -> (a -> a) -> a -> a)
>     ->  \(IO : * -> *)
>     ->  \(return : forall (a : *) -> a -> IO a)
>     ->  \((>>=)
>         :   forall (a : *)
>         ->  forall (b : *)
>         ->  IO a
>         ->  (a -> IO b)
>         ->  IO b
>         )
>     ->  \(putStrLn : String -> IO U)
>     ->  \(getLine : IO String)
> 
>         -- Derived functions
>     ->  (   \((>>) : IO U -> IO U -> IO U)
>         ->  \(two   : Nat)
>         ->  \(three : Nat)
>         ->  \(four  : Nat)
>         ->  \(five  : Nat)
>         ->  \(six   : Nat)
>         ->  \(seven : Nat)
>         ->  \(eight : Nat)
>         ->  \(nine  : Nat)
>         ->  \(ten   : Nat)
>         ->  (   \(replicateM_ : Nat -> IO U -> IO U)
>             ->  \(ninetynine : Nat)
>             ->  replicateM_ ninetynine ((>>=) String U getLine putStrLn)
>             )
> 
>             -- replicateM_
>             (   \(n : Nat)
>             ->  \(io : IO U)
>             ->  foldNat n (IO U) ((>>) io) (return U Unit)
>             )
> 
>             -- ninetynine
>             ((+) ((*) nine ten) nine)
>         )
> 
>         -- (>>)
>         (   \(m : IO U)
>         ->  \(n : IO U)
>         ->  (>>=) U U m (\(_ : U) -> n)
>         )
> 
>         -- two
>         ((+) one one)
> 
>         -- three
>         ((+) one ((+) one one))
> 
>         -- four
>         ((+) one ((+) one ((+) one one)))
> 
>         -- five
>         ((+) one ((+) one ((+) one ((+) one one))))
> 
>         -- six
>         ((+) one ((+) one ((+) one ((+) one ((+) one one)))))
> 
>         -- seven
>         ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one one))))))
> 
>         -- eight
>         ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one one)))))))
>         -- nine
>         ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one one))))))))
> 
>         -- ten
>         ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one ((+) one one)))))))))
>     )
> 
>     -- Nat
>     (   forall (a : *)
>     ->  (a -> a)
>     ->  a
>     ->  a
>     )
> 
>     -- zero
>     (   \(a : *)
>     ->  \(Succ : a -> a)
>     ->  \(Zero : a)
>     ->  Zero
>     )
> 
>     -- one
>     (   \(a : *)
>     ->  \(Succ : a -> a)
>     ->  \(Zero : a)
>     ->  Succ Zero
>     )
> 
>     -- (+)
>     (   \(m : forall (a : *) -> (a -> a) -> a -> a)
>     ->  \(n : forall (a : *) -> (a -> a) -> a -> a)
>     ->  \(a : *)
>     ->  \(Succ : a -> a)
>     ->  \(Zero : a)
>     ->  m a Succ (n a Succ Zero)
>     )
> 
>     -- (*)
>     (   \(m : forall (a : *) -> (a -> a) -> a -> a)
>     ->  \(n : forall (a : *) -> (a -> a) -> a -> a)
>     ->  \(a : *)
>     ->  \(Succ : a -> a)
>     ->  \(Zero : a)
>     ->  m a (n a Succ) Zero
>     )
> 
>     -- foldNat
>     (   \(n : forall (a : *) -> (a -> a) -> a -> a)
>     ->  n
>     )
> 
>     -- IO
>     (   \(r : *)
>     ->  forall (x : *)
>     ->  (String -> x -> x)
>     ->  ((String -> x) -> x)
>     ->  (r -> x)
>     ->  x
>     )
> 
>     -- return
>     (   \(a : *)
>     ->  \(va : a)
>     ->  \(x : *)
>     ->  \(PutStrLn : String -> x -> x)
>     ->  \(GetLine : (String -> x) -> x)
>     ->  \(Return : a -> x)
>     ->  Return va
>     )
> 
>     -- (>>=)
>     (   \(a : *)
>     ->  \(b : *)
>     ->  \(m : forall (x : *)
>         ->  (String -> x -> x)
>         ->  ((String -> x) -> x)
>         ->  (a -> x)
>         ->  x
>         )
>     ->  \(f : a
>         ->  forall (x : *)
>         -> (String -> x -> x)
>         -> ((String -> x) -> x)
>         -> (b -> x)
>         -> x
>         )
>     ->  \(x : *)
>     ->  \(PutStrLn : String -> x -> x)
>     ->  \(GetLine : (String -> x) -> x)
>     ->  \(Return : b -> x)
>     ->  m x PutStrLn GetLine (\(va : a) -> f va x PutStrLn GetLine Return)
>     )
> 
>     -- putStrLn
>     (   \(str : String)
>     ->  \(x : *)
>     ->  \(PutStrLn : String -> x -> x  )
>     ->  \(GetLine  : (String -> x) -> x)
>     ->  \(Return   : U -> x)
>     ->  PutStrLn str (Return Unit)
>     )
> 
>     -- getLine
>     (   \(x : *)
>     ->  \(PutStrLn : String -> x -> x  )
>     ->  \(GetLine  : (String -> x) -> x)
>     ->  \(Return   : String -> x)
>     -> GetLine Return
>     )
> )

If you type-check and normalize this program, the compiler will produce an
unrolled syntax tree representing a program that echoes 99 lines from standard
input to standard output:

> $ morte < recursive.mt
> ∀(String : *) → ∀(U : *) → U → ∀(x : *) → (String → x → x) → ((String → x
> ) → x) → (U → x) → x
> λ(String : *) → λ(U : *) → λ(Unit : U) → λ(x : *) → λ(PutStrLn : String →
>  x → x) → λ(GetLine : (String → x) → x) → λ(Return : U → x) → GetLine (λ(
> va : String) → PutStrLn va (GetLine (λ(va@1 : String) → PutStrLn va@1 (Ge
> tLine (λ(va@2 : String) → PutStrLn va@2 (GetLine (λ(va@3 : String) → PutS
> trLn va@3 (...
> <snip>
> ... GetLine (λ(va@92 : String) → PutStrLn va@92 (GetLine (λ(va@93 : Strin
> g) → PutStrLn va@93 (GetLine (λ(va@94 : String) → PutStrLn va@94 (GetLine
>  (λ(va@95 : String) → PutStrLn va@95 (GetLine (λ(va@96 : String) → PutStr
> Ln va@96 (GetLine (λ(va@97 : String) → PutStrLn va@97 (GetLine (λ(va@98 :
>  String) → PutStrLn va@98 (Return Unit)))))))))))))))))))))))))))))))))))
> )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
> )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
> )))))))))))))))))

    This program can then be passed to a backend language which interprets the
    syntax tree, translating @GetLine@ and @PutStrLn@ to read and write
    commands.

    Notice that although our program is built using the high-level @replicateM_@
    function, you'd never be able to tell by looking at the optimized program.
    By encoding effects as a free monad, we expose the monad laws to Morte,
    which allows the normalizer to optimize away monadic abstractions like
    @replicateM_@.
-}

{- $portability
    You can use Morte as a standard format for transmitting code between
    functional languages.  This requires you to encode the source language to
    Morte and decode the Morte into the destination language.

    If every functional language has a Morte encoder/decoder, then eventually
    there can be a code utility analogous to @pandoc@ that converts code written
    any of these languages to code written in any other of these language.

    Additionally, Morte provides a standard `Data.Binary.Binary` interface that
    you can use for serializing and deserializing code.  You may find this
    useful for transmitting code between distributed services, even within
    the same language.
-}
