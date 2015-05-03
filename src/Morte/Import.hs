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

    > morte: 
    > ⤷ #foo
    > ⤷ #bar
    > Cyclic import: #foo

    You can also import expressions hosted on network endpoints.  Just use a
    hashtag followed by a URL:

    > #http://host[:port]/path

    For example, if our @id@ expression were hosted at @http://example.com/id@,
    then we would embed the expression within our code using:

    > #http://example.com/id

    Or if the @id@ expression were hosted locally on port 8000, you would write:

    > #http://localhost:8000/id
-}

module Morte.Import (
    -- * Import
      load
    , Cycle(..)
    , Imported(..)
    ) where

import Control.Exception (Exception, throwIO)
import Control.Monad (join)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Managed (Managed, managed, with)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Encoding as Text
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import Data.Traversable (traverse)
import Data.Typeable (Typeable)
import Filesystem as Filesystem
import Lens.Family (LensLike')
import Lens.Family.State.Strict (zoom)
import Network.HTTP.Client (Manager)
import qualified Network.HTTP.Client as HTTP
import qualified Network.HTTP.Client.TLS as HTTP
import Prelude hiding (FilePath)

import Morte.Core (Expr, Path(..), X(..), buildPath, typeOf)
import Morte.Parser (exprFromText)

builderToString :: Builder -> String
builderToString = Text.unpack . Builder.toLazyText

-- | An import failed because of a cycle import
newtype Cycle = Cycle
    { cyclicImport :: Path  -- ^ The offending cyclic import
    }
  deriving (Typeable)

instance Exception Cycle

instance Show Cycle where
    show (Cycle path) = "Cyclic import: " ++ builderToString (buildPath path)

-- | Extend another exception with the current import stack
data Imported e = Imported
    { importStack :: [Path] -- ^ Imports resolved so far
    , nested      :: e      -- ^ The nested exception
    } deriving (Typeable)

instance Exception e => Exception (Imported e)

instance Show e => Show (Imported e) where
    show (Imported paths e) =
            "\n"
        ++  unlines
                (map (\path -> "⤷ " ++ builderToString (buildPath path)) paths)
        ++  show e

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

needManager :: StateT Status Managed Manager
needManager = do
    x <- zoom manager get
    case x of
        Just m  -> return m
        Nothing -> do
            let settings = HTTP.tlsManagerSettings
                    { HTTP.managerResponseTimeout = Just 1000000 }  -- 1 second
            m <- lift (managed (HTTP.withManager settings))
            zoom manager (put (Just m))
            return m

-- | Load a `Path` as a \"dynamic\" expression (without resolving any imports)
loadDynamic :: Path -> StateT Status Managed (Expr Path)
loadDynamic p = do
    txt <- case p of
        File file -> do
            liftIO (fmap Text.fromStrict (Filesystem.readTextFile file))
        URL  url  -> do
            request  <- liftIO (HTTP.parseUrl url)
            m        <- needManager
            response <- liftIO (HTTP.httpLbs request m)
            case Text.decodeUtf8' (HTTP.responseBody response) of
                Left  err -> liftIO (throwIO err)
                Right txt -> return txt
    case exprFromText txt of
        Left  err  -> do
            paths <- zoom stack get
            liftIO (throwIO (Imported paths err))
        Right expr -> return expr 

-- | Load a `Path` as a \"static\" expression (with all imports resolved)
loadStatic :: Path -> StateT Status Managed (Expr X)
loadStatic path = do
    paths <- zoom stack get
    let paths' = paths ++ [path]
    zoom stack (put $! paths')
    expr <- if path `elem` paths
        then liftIO (throwIO (Imported paths (Cycle path)))
        else do
            m <- zoom cache get
            case Map.lookup path m of
                Just expr -> return expr
                Nothing   -> do
                    expr' <- loadDynamic path
                    case traverse (\_ -> Nothing) expr' of
                        Just expr -> do
                            zoom cache (put $! Map.insert path expr m)
                            return expr
                        Nothing   -> fmap join (traverse loadStatic expr')
    case typeOf expr of
        Left  err -> liftIO (throwIO (Imported paths' err))
        Right _   -> return ()
    zoom stack (put paths)
    return expr

-- | Resolve all imports within an expression
load :: Expr Path -> IO (Expr X)
load expr = with
    (evalStateT (fmap join (traverse loadStatic expr)) status)
    return
  where
    status = Status [] Map.empty Nothing
