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
