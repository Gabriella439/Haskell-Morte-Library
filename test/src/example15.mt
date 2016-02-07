-- corecursive.mt

-- data IOF r s = PutStrLn String s | GetLine (String -> s) | Return r
--
-- data IO r = forall s . MkIO s (s -> IOF r s)
--
-- main = MkIO Nothing (maybe (\str -> PutStrLn str Nothing) (GetLine Just))

(   \(String : *)
->  (   \(Maybe : * -> *)
    ->  \(Just : forall (a : *) -> a -> Maybe a)
    ->  \(Nothing : forall (a : *) -> Maybe a)
    ->  \(  maybe
        :   forall (a : *) -> Maybe a -> forall (x : *) -> (a -> x) -> x -> x
        )
    ->  \(IOF : * -> * -> *)
    ->  \(  PutStrLn
        :   forall (r : *)
        ->  forall (s : *)
        ->  String
        ->  s
        ->  IOF r s
        )
    ->  \(  GetLine
        :   forall (r : *)
        ->  forall (s : *)
        ->  (String -> s)
        ->  IOF r s
        )
    ->  \(  Return
        :   forall (r : *)
        ->  forall (s : *)
        ->  r
        ->  IOF r s
        )
    ->  (   \(IO : * -> *)
        ->  \(  MkIO
            :   forall (r : *) -> forall (s : *) -> s -> (s -> IOF r s) -> IO r
            )
        ->  (   \(main : forall (r : *) -> IO r)
            ->  main
            )

            -- main
            (   \(r : *)
            ->  MkIO
                r
                (Maybe String)
                (Nothing String)
                (   \(m : Maybe String)
                ->  maybe
                        String
                        m
                        (IOF r (Maybe String))
                        (\(str : String) ->
                            PutStrLn r (Maybe String) str (Nothing String)
                        )
                        (GetLine r (Maybe String) (Just String))
                )
            )
        )

        -- IO
        (   \(r : *)
        ->  forall (x : *)
        ->  (forall (s : *) -> s -> (s -> IOF r s) -> x)
        ->  x
        )

        -- MkIO
        (   \(r : *)
        ->  \(s : *)
        ->  \(seed : s)
        ->  \(step : s -> IOF r s)
        ->  \(x : *)
        ->  \(k : forall (s : *) -> s -> (s -> IOF r s) -> x)
        ->  k s seed step
        )
    )

    -- Maybe
    (\(a : *) -> forall (x : *) -> (a -> x) -> x -> x)

    -- Just
    (   \(a : *)
    ->  \(va : a)
    ->  \(x : *)
    ->  \(Just : a -> x)
    ->  \(Nothing : x)
    ->  Just va
    )

    -- Nothing
    (   \(a : *)
    ->  \(x : *)
    ->  \(Just : a -> x)
    ->  \(Nothing : x)
    ->  Nothing
    )

    -- maybe
    (\(a : *) -> \(m : forall (x : *) -> (a -> x) -> x -> x) -> m)

    -- IOF
    (   \(r : *)
    ->  \(s : *)
    ->  forall (x : *)
    ->  (String -> s -> x)
    ->  ((String -> s) -> x)
    ->  (r -> x)
    ->  x
    )

    -- PutStrLn
    (   \(r : *)
    ->  \(s : *)
    ->  \(str : String)
    ->  \(vs : s)
    ->  \(x : *)
    ->  \(PutStrLn : String -> s -> x)
    ->  \(GetLine : (String -> s) -> x)
    ->  \(Return : r -> x)
    ->  PutStrLn str vs
    )

    -- GetLine
    (   \(r : *)
    ->  \(s : *)
    ->  \(k : String -> s)
    ->  \(x : *)
    ->  \(PutStrLn : String -> s -> x)
    ->  \(GetLine : (String -> s) -> x)
    ->  \(Return : r -> x)
    ->  GetLine k
    )

    -- Return
    (   \(r : *)
    ->  \(s : *)
    ->  \(vr : r)
    ->  \(x : *)
    ->  \(PutStrLn : String -> s -> x)
    ->  \(GetLine : (String -> s) -> x)
    ->  \(Return : r -> x)
    ->  Return vr
    )

)
