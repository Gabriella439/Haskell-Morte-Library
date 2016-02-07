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
