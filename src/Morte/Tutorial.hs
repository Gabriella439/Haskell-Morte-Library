{-| Morte is a minimalist implementation of the calculus of constructions that
    comes with a parser, type-checker, optimizer, and pretty-printer.

    You can think of Morte as a very low-level virtual machine for functional
    languages.  This virtual machine was designed with the following design
    principles:

    * Be simple - so people can reason about Morte's soundness

    * Be portable - so you can transmit code, even between different languages

    * Be efficient - so that Morte can scale to large code bases

    * Be super-optimizable - by disabling unrestricted recursion

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

    -- ** let
    -- $let

    -- ** Simple types
    -- $types

    -- ** newtypes
    -- $newtypes

    -- ** Recursion
    -- $recursion
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

    The second-to-last output line is the type of our program as computed by the
    compiler.  Compare it with the equivalent Haskell type:

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

    * @let@

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
    desugar these abstractions.
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
    already recognize special cases of this technique as CPS-encoding or
    Church-encoding.

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
    @Bool@ type.

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

    This is also equal to our previous program.

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

    Here's another example, using natural numbers:

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

    You might wonder why Morte forbids recursion, forcing us to encode data
    types this way.  Morte imposes this restriction this in order to
    super-optimize your program.  For example, consider the following
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
    library to mechanically check that the two programs are equal:

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

    We just mechanically proven that @map id == id@.  When we transform our code
    to a non-recursive form we've done most of the work.  The compiler can then
    check that the two programs are equal by just optimizing both programs and
    verifying that they produce identical optimized code.

    Using this same trick we can also prove the other map fusion law:

> map (f . g) = map f . map g

    Here is the first program:

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

    ... and here is the second program:

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

    Verify using the library that those produce identical expressions.  For
    reference, they both generate the following type and optimized program that
    loops over the list just once, applying @\'f\'@ and @\'g\'@ to every value:

> $ morte < mapcomp1.mt
> ∀(a : *) → ∀(b : *) → ∀(c : *) → (b → c) → (a → b) → (∀(x : *) → (a → x → x) → x → x) → ∀(x : *) → (c → x → x) → x → x
> λ(a : *) → λ(b : *) → λ(c : *) → λ(f : b → c) → λ(g : a → b) → λ(l : ∀(x : *) → (a → x → x) → x → x) → λ(x : *) → λ(Cons : c → x → x) → l x (λ(va : a) → Cons (f (g va)))

-}
