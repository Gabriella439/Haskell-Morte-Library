(  \(Nat : *)
-> \(Succ : Nat -> Nat)
-> \(Zero : Nat)
-> \(mult : Nat -> Nat -> Nat)
-> \(foldNat : Nat -> forall (r : *) -> (r -> r) -> r -> r)
-> \(Pair : * -> *)
-> \(_P    : forall (a : *) -> a -> a -> Pair a)
-> \(_fst  : forall (a : *) -> Pair a -> a)
-> \(_snd  : forall (a : *) -> Pair a -> a)
-> (  \(NPair : *)
   -> \(P : Nat -> Nat -> NPair)
   -> \(fst : NPair -> Nat)
   -> \(snd : NPair -> Nat)
   -> \(mi  : Nat)
   -> \(n : Nat)
   -> (  \(pfact : NPair -> NPair) 
      -> snd (foldNat n NPair pfact (P Zero mi))
      )

      (  \(p : NPair)
      -> (\(sfp : Nat) -> P sfp (mult (snd p) sfp)) (Succ (fst p))
      )
   )

  -- NPair
  (Pair Nat)

  -- P
  (_P Nat)

  -- fst
  (_fst Nat)

  -- snd
  (_snd Nat)

  -- multiplicative identity
  (Succ Zero)

  -- 7
  (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))

)

-- Nat
(forall (nat : *) -> (nat -> nat) -> nat -> nat)

-- Succ data constructor
(  \(n : forall (nat : *) -> (nat -> nat) -> nat -> nat)
-> \(nat : *)
-> \(Succ : nat -> nat)
-> \(Zero : nat)
-> Succ (n nat Succ Zero)
)

-- Zero data constructor
(  \(nat : *)
-> \(Succ : nat -> nat)
-> \(Zero : nat)
-> Zero
)

-- mult
(  \(a : |~| (nat : *) -> (nat -> nat) -> nat -> nat)
-> \(b : forall (nat : *) -> (nat -> nat) -> nat -> nat)
-> \(nat : *)
-> \(Succ : nat -> nat)
-> \(Zero : nat)
-> (a nat) (b nat Succ) Zero
)

-- foldNat
(  \(n : forall (r : *) -> (r -> r) -> r -> r)
-> n
)

-- MonoPair
(\(a : *) -> forall (r : *) -> (a -> a -> r) -> r)

-- P
(  \(a : *)
-> \(va : a)
-> \(vb : a)
-> \(r : *)
-> \(Pair : a -> a -> r)
-> Pair va vb
)

-- fst
(  \(a : *)
-> \(p : forall (r : *) -> (a -> a -> r) -> r)
-> p a (\(x : a) -> \(_ : a) -> x)
)

-- snd
(  \(a : *)
-> \(p : forall (r : *) -> (a -> a -> r) -> r)
-> p a (\(_ : a) -> \(x : a) -> x)
)
