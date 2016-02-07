-- id2.mt

(   \(id : forall (a : *) -> a -> a)
->  id (forall (a : *) -> a -> a) id  -- Apply the identity function to itself
)

-- id
(\(a : *) -> \(x : a) -> x)
