{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wall #-}

{-| Morte lets you import external expressions located either in local files or
    hosted on network endpoints.

    To import a local file as an expression, just prepend the file path with a
    hash tag.  For example, suppose we had the following three local files:

    > -- id
    > \(a : *) -> \(x : a) -> x

    > -- Bool
    > forall (Bool : *) -> forall (True : Bool) -> forall (False : Bool) -> True

    > -- True
    > \(Bool : *) -> \(True : Bool) -> \(False : Bool) -> True

    You could then reference them within a Morte expression using this syntax:

    > #id #Bool #True

    ... which would embed their expressions directly within the syntax tree:

    > -- ... expands out to:
    > (\(a : *) -> \(x : a) -> x)
    >     (forall (Bool : *) -> forall (True : Bool) -> forall (False : Bool) -> True)
    >     (\(Bool : *) -> \(True : Bool) -> \(False : Bool) -> True)

    Imported expressions may contain imports of their own, too, which will
    continue to be resolved.  However, Morte will prevent cyclic imports.  For
    example, if you had these two files:

    > -- foo
    > #bar

    > -- bar
    > #foo

    ... Morte would throw the following exception if you tried to import @foo@:

    > morte: ImportError {importStack = [IsFile (FilePath "bar"),IsFile (FilePath "foo")], cyclicImport = IsFile (FilePath "foo")}

    You can also import expressions hosted on network endpoints.  Just use this
    syntax:

    > @host:port/path

    For example, if our @id@ expression were hosted at
    @https://example.com:1999/id@, then we would use:

    > -- Note: no 'https://'
    > @example.com:1999/id

    If you omit the port, Morte will default to the standard Morte port of 1999:

    > -- Same thing
    > @example.com/id

    Also, if you omit the host, Morte will default to @localhost@:

    > -- Equivalent to: @localhost/id
    > /id
-}

module Morte.Import (
    -- * Import
      load
    , ImportError(..)
    ) where

import Control.Applicative (Applicative(..))
import Control.Exception (Exception, throwIO)
import Control.Monad (join)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Managed (Managed, managed, with)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Data.Default.Class (def)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Encoding as Text
import Data.Traversable (traverse)
import Data.Typeable (Typeable)
import Filesystem as Filesystem
import Lens.Family (LensLike')
import Lens.Family.State.Strict (zoom)
import Network.HTTP.Client (Manager)
import qualified Network.HTTP.Client as HTTP
import qualified Network.HTTP.Client.TLS as HTTP
import Prelude hiding (FilePath)

import Morte.Core (Expr, Path(..), URL(..), X(..))
import Morte.Parser (exprFromText)

-- | An import expression failed because of a cyclic import
data ImportError = ImportError
    { importStack :: [Path] -- ^ Imports resolved so far
    , cyclicImport :: Path  -- ^ The offending cyclic import
    }
  deriving (Typeable, Show)

instance Exception ImportError

data Status = Status
    { _stack   :: [Path]
    , _cache   :: Map Path (Expr X)
    , _manager :: Maybe Manager
    }

stack :: Functor f => LensLike' f Status [Path]
stack k s = fmap (\x -> s { _stack = x }) (k (_stack s))

cache :: Functor f => LensLike' f Status (Map Path (Expr X))
cache k s = fmap (\x -> s { _cache = x }) (k (_cache s))

manager :: Functor f => LensLike' f Status (Maybe Manager)
manager k s = fmap (\x -> s { _manager = x }) (k (_manager s))

newtype Load a = Load { runLoad :: StateT Status Managed a }

instance Functor Load where
    fmap f (Load m) = Load (fmap f m)

instance Applicative Load where
    pure a = Load (pure a)

    Load mf <*> Load mx = Load (mf <*> mx)

instance Monad Load where
    return a = Load (return a)

    m >>= f = Load (runLoad m >>= \x -> runLoad (f x))

instance MonadIO Load where
    liftIO io = Load (liftIO io)

needManager :: Load Manager
needManager = Load (do
    x <- zoom manager get
    case x of
        Just m  -> return m
        Nothing -> do
            m <- lift (managed (HTTP.withManager HTTP.tlsManagerSettings))
            zoom manager (put (Just m))
            return m )

-- | Load a `Path` as a \"dynamic\" expression (without resolving any imports)
loadDynamic :: Path -> Load (Expr Path)
loadDynamic p = do
    txt <- case p of
        IsFile file -> do
            liftIO (fmap Text.fromStrict (Filesystem.readTextFile file))
        IsURL  url  -> do
            let request = def
                    { HTTP.host = urlHost url
                    , HTTP.port = urlPort url
                    , HTTP.path = urlPath url
                    }
            m        <- needManager
            response <- liftIO (HTTP.httpLbs request m)
            case Text.decodeUtf8' (HTTP.responseBody response) of
                Left  err -> liftIO (throwIO err)
                Right txt -> return txt
    case exprFromText txt of
        Left  err  -> liftIO (throwIO err)
        Right expr -> return expr 

-- | Load a `Path` as a \"static\" expression (with all imports resolved)
loadStatic :: Path -> Load (Expr X)
loadStatic path = Load (do
    paths <- zoom stack get
    if path `elem` paths
        then liftIO (throwIO (ImportError paths path))
        else do
            m <- zoom cache get
            case Map.lookup path m of
                Just expr -> return expr
                Nothing   -> do
                    expr' <- runLoad (loadDynamic path)
                    case traverse (\_ -> Nothing) expr' of
                        Just expr -> do
                            zoom cache (put $! Map.insert path expr m)
                            return expr
                        Nothing   -> do
                            zoom stack (put $! path:paths)
                            expr <- runLoad
                                (fmap join (traverse loadStatic expr'))
                            zoom stack (put paths)
                            return expr )

-- | Resolve all imports within an expression
load :: Expr Path -> IO (Expr X)
load expr = with
    (evalStateT (runLoad (fmap join (traverse loadStatic expr))) status)
    return
  where
    status = Status [] Map.empty Nothing
