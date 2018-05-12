# Morte v1.6.19

Morte is a super-optimizing intermediate language for functional languages.

`morte` centers around a single idea: a strongly normalizing, typed, and
polymorphic lambda calculus is the ideal language for super-optimization of
programs.  Optimization is just normalization of lambda terms.  All abstractions
desugar to lambda abstraction.

## Quick start

* Install [the `stack` tool](http://haskellstack.org/)
* `stack setup`
* `stack install morte`

This creates the `morte` executable under `stack`'s default `bin` directory
(typically `~/.local/bin/` on Unix-like systems).  This executable reads Morte
expressions from `stdin`, type-checks them, outputs their type to `stderr` and
outputs the optimized program to `stdout`.  For example:

    $ morte
    \(a : *) -> \(x : a) -> x <Enter>
    <Ctrl-D>
    ∀(a : *) → a → a
    
    λ(a : *) → λ(x : a) → x
    $ # There was nothing to optimize

To learn more, read the
[Morte tutorial](http://hackage.haskell.org/package/morte/docs/Morte-Tutorial.html).

You can also use a front-end. Current front ends are

- [Annah](https://github.com/Gabriel439/Haskell-Annah-Library)

with hopefully more to come.

## How to contribute

Morte needs a front-end compiler to translate high-level abstractions to the
calculus of constructions and a back-end compiler to translate Morte to an
executable.  I'm currently working on both of these, but if you would like to
contribute then contact me or open an issue on the issue tracker to discuss
this.

## Development Status

[![Build Status](https://travis-ci.org/Gabriel439/Haskell-Morte-Library.png)](https://travis-ci.org/Gabriel439/Haskell-Morte-Library)

The main volatility in the API is in error reporting, specifically how to
preserve better error messages for front-end compilers.

Additionally, `morte` may eventually switch to using `attoparsec` instead of
`alex`/`happy`.  When this happens it might affect the grammar in subtle and
unanticipated ways.

`morte` may also eventually expand the grammar and introduce other syntactic
niceties, but I'm currently playing it safe and keeping the grammar small for
now.

One feature I'd eventually like to implement is the use of free theorems to
further simplify Morte code, but this is not urgent and definitely a lower
priority than implementing front-end and back-end compilers.  If implemented,
this would be entirely backwards compatible.

## Regenerating .travis.yml

Using https://github.com/hvr/multi-ghc-travis

```
../multi-ghc-travis/make_travis_yml.hs morte.cabal alex-3.1.4 happy-1.19.5 > .travis.yml
```

You need to put this in the ```before_install``` section so that cabal can find alex and happy:

```
 - export HAPPYVER=1.19.5
 - export ALEXVER=3.1.4
 - export PATH=/opt/ghc/$GHCVER/bin:/opt/cabal/$CABALVER/bin:/opt/happy/$HAPPYVER/bin:/opt/alex/$ALEXVER/bin:$PATH
```

## License (BSD 3-clause)

Copyright (c) 2014 Gabriel Gonzalez
All rights reserved.

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice, this
  list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright notice, this
  list of conditions and the following disclaimer in the documentation and/or
  other materials provided with the distribution.

* Neither the name of Gabriel Gonzalez nor the names of other contributors may
  be used to endorse or promote products derived from this software without
  specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
