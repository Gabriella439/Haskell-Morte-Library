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
