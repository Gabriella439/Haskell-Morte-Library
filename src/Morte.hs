{-| This module is the recommended entry point for @morte@, exporting all
    functions from this library's public interface

    If you are new to @morte@, read "Morte.Tutorial" to learn more about the
    motivation behind this library and how to use @morte@.
-}

module Morte (
    -- Re-exports
    -- $reexports
    module Morte.Core,
    module Morte.Parser,
) where

import Morte.Core
import Morte.Parser

{- $reexports
    "Morte.Core" contains the core calculus for the library.

    Use "Morte.Parser" to parse Morte expressions from `Data.Text.Lazy.Text`.

    Read "Morte.Tutorial" to learn how to use this library.
-}
