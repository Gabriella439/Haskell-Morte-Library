{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings  #-}
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

    The compiler expects the downloaded expressions to be in the same format 
    as local files, specifically UTF8-encoded source code text.

    For example, if our @id@ expression were hosted at @http://example.com/id@,
    then we would embed the expression within our code using:

    > #http://example.com/id

    You can also reuse directory names as expressions.  If you provide a path
    to a local or remote directory then the compiler will look for a file named
    @\@@ within that directory and use that file to represent the directory.
-}

module Morte.Import (
    -- * Import
      load
    , Cycle(..)
    , ReferentiallyOpaque(..)
    , Imported(..)
    ) where

import Control.Exception (Exception, IOException, catch, onException, throwIO)
import Control.Monad (join)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Managed (Managed, managed, with)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Monoid ((<>))
import Data.Text.Buildable (build)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Encoding as Text
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import Data.Traversable (traverse)
import Data.Typeable (Typeable)
import Filesystem.Path ((</>))
import Filesystem as Filesystem
import Lens.Micro (Lens')
import Lens.Micro.Mtl (zoom)
import Network.HTTP.Client (Manager)
import qualified Network.HTTP.Client as HTTP
import qualified Network.HTTP.Client.TLS as HTTP
import Prelude hiding (FilePath)

import Morte.Core (Expr, Path(..), X(..), typeOf)
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
    show (Cycle path) = "Cyclic import: " ++ builderToString (build path)

{-| Morte tries to ensure that all expressions hosted on network endpoints are
    weakly referentially transparent, meaning roughly that any two clients will
    compile the exact same result given the same URL.

    To be precise, a strong interpretaton of referential transparency means that
    if you compiled a URL you could replace the expression hosted at that URL
    with the compiled result.  Let's term this \"static linking\".  Morte (very
    intentionally) does not satisfy this stronger interpretation of referential
    transparency since \"statically linking\" an expression (i.e. permanently
    resolving all imports) means that the expression will no longer update if
    its dependencies change.

    In general, either interpretation of referential transparency is not
    enforceable in a networked context since one can easily violate referential
    transparency with a custom DNS, but Morte can still try to guard against
    common unintentional violations.  To do this, Morte enforces that a
    non-local import may not reference a local import.

    Local imports are defined as:

    * A file

    * A URL with a host of @localhost@ or @127.0.0.1@

    All other imports are defined to be non-local
-}
newtype ReferentiallyOpaque = ReferentiallyOpaque
    { opaqueImport :: Path  -- ^ The offending opaque import
    } deriving (Typeable)

instance Exception ReferentiallyOpaque

instance Show ReferentiallyOpaque where
    show (ReferentiallyOpaque path) =
        "Referentially opaque import: " ++ builderToString (build path)

-- | Extend another exception with the current import stack
data Imported e = Imported
    { importStack :: [Path] -- ^ Imports resolved so far, in reverse order
    , nested      :: e      -- ^ The nested exception
    } deriving (Typeable)

instance Exception e => Exception (Imported e)

instance Show e => Show (Imported e) where
    show (Imported paths e) =
            "\n"
        ++  unlines (map (\path -> "⤷ " ++ builderToString (build path))
                         (reverse paths) )
        ++  show e

data Status = Status
    { _stack   :: [Path]
    , _cache   :: Map Path (Expr X)
    , _manager :: Maybe Manager
    }

stack :: Lens' Status [Path]
stack k s = fmap (\x -> s { _stack = x }) (k (_stack s))

cache :: Lens' Status (Map Path (Expr X))
cache k s = fmap (\x -> s { _cache = x }) (k (_cache s))

manager :: Lens' Status (Maybe Manager)
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
    paths <- zoom stack get
    txt <- case p of
        File file -> do
            let readFile' = do
                    Filesystem.readTextFile file `catch` (\e -> do
                    -- Unfortunately, GHC throws an `InappropriateType`
                    -- exception when trying to read a directory, but does not
                    -- export the exception, so I must resort to a more
                    -- heavy-handed `catch`
                    let _ = e :: IOException
                    -- If the fallback fails, reuse the original exception to
                    -- avoid user confusion
                    Filesystem.readTextFile (file </> "@")
                        `onException` throwIO e )
            liftIO (fmap Text.fromStrict readFile')
        URL  url  -> do
            request  <- liftIO (HTTP.parseUrl url)
            m        <- needManager
            let httpLbs' = do
                    HTTP.httpLbs request m `catch` (\e -> case e of
                        HTTP.StatusCodeException _ _ _ -> do
                            let request' = request
                                    { HTTP.path = HTTP.path request <> "/@" }
                            -- If the fallback fails, reuse the original
                            -- exception to avoid user confusion
                            HTTP.httpLbs request' m `onException` throwIO e
                        _ -> throwIO e )
            response <- liftIO httpLbs'
            case Text.decodeUtf8' (HTTP.responseBody response) of
                Left  err -> liftIO (throwIO err)
                Right txt -> return txt

    let abort err = liftIO (throwIO (Imported paths err))
    case exprFromText txt of
        Left  err  -> case p of
            URL url -> do
                -- Also try the fallback in case of a parse error, since the
                -- parse error might signify that this URL points to a directory
                -- list
                request  <- liftIO (HTTP.parseUrl url)
                let request' = request { HTTP.path = HTTP.path request <> "/@" }
                m        <- needManager
                response <- liftIO
                    (HTTP.httpLbs request' m `onException` abort err)
                case Text.decodeUtf8' (HTTP.responseBody response) of
                    Left  _    -> liftIO (abort err)
                    Right txt' -> case exprFromText txt' of
                        Left  _    -> liftIO (abort err)
                        Right expr -> return expr
            _      -> liftIO (abort err)
        Right expr -> return expr 

-- | Load a `Path` as a \"static\" expression (with all imports resolved)
loadStatic :: Path -> StateT Status Managed (Expr X)
loadStatic path = do
    paths <- zoom stack get

    let local (URL url) = case HTTP.parseUrl url of
            Nothing      -> False
            Just request -> case HTTP.host request of
                "127.0.0.1" -> True
                "localhost" -> True
                _           -> False
        local (File _)  = True
    case paths of
        parent:_ ->
            if local path && not (local parent)
            then liftIO (throwIO (Imported paths (ReferentiallyOpaque path)))
            else return ()
        _        -> return ()

    let paths' = path:paths
    zoom stack (put paths')
    (expr, cached) <- if path `elem` paths
        then liftIO (throwIO (Imported paths (Cycle path)))
        else do
            m <- zoom cache get
            case Map.lookup path m of
                Just expr -> return (expr, True)
                Nothing   -> do
                    expr'  <- loadDynamic path
                    expr'' <- case traverse (\_ -> Nothing) expr' of
                        -- No imports left
                        Just expr -> do
                            zoom cache (put $! Map.insert path expr m)
                            return expr
                        -- Some imports left, so recurse
                        Nothing   -> fmap join (traverse loadStatic expr')
                    return (expr'', False)

    -- Type-check expressions here for two separate reasons:
    --
    --  * to verify that they are closed
    --  * to catch type errors as early in the import process as possible
    --
    -- There is no need to check expressions that have been cached, since they
    -- have already been checked
    if cached
        then return ()
        else case typeOf expr of
            Left  err -> liftIO (throwIO (Imported paths' err))
            Right _   -> return ()

    zoom stack (put paths)

    return expr

-- | Resolve all imports within an expression
load :: Expr Path -> IO (Expr X)
load expr =
    with (evalStateT (fmap join (traverse loadStatic expr)) status) return
  where
    status = Status [] Map.empty Nothing
