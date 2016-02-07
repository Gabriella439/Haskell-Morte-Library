-- id.mt

-- Morte accepts comments

-- Also, whitespace is not significant
\(String : *) ->
    (\(a : *) -> \(x : a) -> x) String
