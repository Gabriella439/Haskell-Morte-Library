{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor              #-}

-- | All `Context`-related operations

module Morte.Context (
    -- * Context
      Context(..)
    , empty
    , insert
    , lookup
    , toList
    ) where

import Control.DeepSeq (NFData)
import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import Data.Monoid ((<>))
import Data.Sequence (Seq)
import Data.Text.Lazy (Text)
import Prelude hiding (lookup)

import qualified Data.Foldable       as Foldable
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Sequence       as Seq

{-| Bound variable names and their types

    Variable names may appear more than once in the `Context`.  The `Var` @x\@n@
    refers to the @n@th occurrence of @x@ in the `Context` (using 0-based
    numbering).
-}
newtype Context a = Context { getContext :: HashMap Text (Seq a) }
    deriving (Functor, NFData, Show)

{-| An empty context with no key-value pairs

> toList empty = []
-}
empty :: Context a
empty = Context HashMap.empty

-- | Add a key-value pair to the `Context`
insert :: Text -> a -> Context a -> Context a
insert k v =
    Context . HashMap.insertWith (<>) k (Seq.singleton v) . getContext

{-| Lookup a key by name and index

> lookup k 0 (insert k v0              ctx ) = Just v0
> lookup k 1 (insert k v0 (insert k v1 ctx)) = Just v1
-}
lookup :: Text -> Int -> Context a -> Maybe a
lookup x n ctx = do
    val <- HashMap.lookup x (getContext ctx)
    return (Seq.index val n)

-- | Return all key-value associations as a list
toList :: Context a -> [(Text, a)]
toList =
        concatMap (\(k, vs) -> map (\v -> (k, v)) (Foldable.toList vs))
    .   HashMap.toList
    .   getContext
