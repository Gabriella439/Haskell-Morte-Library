-- recursive.mt

-- The Haskell code we will translate to Morte:
--
--     import Prelude hiding (
--         (+), (*), IO, putStrLn, getLine, (>>=), (>>), return )
-- 
--     -- Simple prelude
--
--     data Nat = Succ Nat | Zero
--
--     zero :: Nat
--     zero = Zero
--
--     one :: Nat
--     one = Succ Zero
--
--     (+) :: Nat -> Nat -> Nat
--     Zero   + n = n
--     Succ m + n = m + Succ n
--
--     (*) :: Nat -> Nat -> Nat
--     Zero   * n = Zero
--     Succ m * n = n + (m * n)
--
--     foldNat :: Nat -> (a -> a) -> a -> a
--     foldNat  Zero    f x = x
--     foldNat (Succ m) f x = f (foldNat m f x)
--
--     data IO r = PutStrLn String (IO r) | GetLine (String -> IO r) | Return r
--
--     putStrLn :: String -> IO U
--     putStrLn str = PutStrLn str (Return Unit)
--
--     getLine :: IO String
--     getLine = GetLine Return
--
--     return :: a -> IO a
--     return = Return
--
--     (>>=) :: IO a -> (a -> IO b) -> IO b
--     PutStrLn str io >>= f = PutStrLn str (io >>= f)
--     GetLine k       >>= f = GetLine (\str -> k str >>= f)
--     Return r        >>= f = f r
--
--     -- Derived functions
--
--     (>>) :: IO U -> IO U -> IO U
--     m >> n = m >>= \_ -> n
--
--     two :: Nat
--     two = one + one
--
--     three :: Nat
--     three = one + one + one
--
--     four :: Nat
--     four = one + one + one + one
--
--     five :: Nat
--     five = one + one + one + one + one
--
--     six :: Nat
--     six = one + one + one + one + one + one
--
--     seven :: Nat
--     seven = one + one + one + one + one + one + one
--
--     eight :: Nat
--     eight = one + one + one + one + one + one + one + one
--
--     nine :: Nat
--     nine = one + one + one + one + one + one + one + one + one
--
--     ten :: Nat
--     ten = one + one + one + one + one + one + one + one + one + one
--
--     replicateM_ :: Nat -> IO U -> IO U
--     replicateM_ n io = foldNat n (io >>) (return Unit)
--
--     ninetynine :: Nat
--     ninetynine = nine * ten + nine
--
--     main_ :: IO U
--     main_ = getLine >>= putStrLn

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
