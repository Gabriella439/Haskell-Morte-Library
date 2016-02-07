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
