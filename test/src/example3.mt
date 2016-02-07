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
