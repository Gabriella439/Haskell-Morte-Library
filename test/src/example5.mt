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
