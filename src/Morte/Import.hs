{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}

module Morte.Import (
    -- * Import
      load
    , ImportError(..)
    ) where

import Control.Applicative (Applicative)
import Control.Exception (Exception, throwIO)
import Control.Monad (join)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Managed (Managed, managed, with)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Data.Binary (decodeOrFail)
import Data.Default.Class (def)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Encoding as Text
import Data.Traversable (traverse)
import Data.Typeable (Typeable)
import Data.Void (Void)
import Filesystem as Filesystem
import Lens.Family (LensLike')
import Lens.Family.State.Strict (zoom)
import Lens.Family.TH (makeLenses)
import Network.HTTP.Client (Manager)
import qualified Network.HTTP.Client as HTTP
import qualified Network.HTTP.Client.TLS as HTTP
import Prelude hiding (FilePath)

import Morte.Core (Expr, Path(..), URL(..))
import Morte.Parser (exprFromText)

data ImportError = ImportError
    { importStack :: [Path]
    , cyclicImport :: Path
    }
  deriving (Typeable, Show)

instance Exception ImportError

data Status = Status
    { _stack   :: [Path]
    , _cache   :: HashMap Path (Expr Void)
    , _manager :: Maybe Manager
    }

makeLenses ''Status
stack   :: Functor f => LensLike' f Status [Path]
cache   :: Functor f => LensLike' f Status (HashMap Path (Expr Void))
manager :: Functor f => LensLike' f Status (Maybe Manager)

newtype Load a = Load { runLoad :: StateT Status Managed a }
    deriving (Functor, Applicative, Monad, MonadIO)

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
loadStatic :: Path -> Load (Expr Void)
loadStatic path = Load (do
    paths <- zoom stack get
    if path `elem` paths
        then liftIO (throwIO (ImportError paths path))
        else do
            m <- zoom cache get
            case HashMap.lookup path m of
                Just expr -> return expr
                Nothing   -> do
                    expr' <- runLoad (loadDynamic path)
                    case traverse (\_ -> Nothing) expr' of
                        Just expr -> do
                            zoom cache (put $! HashMap.insert path expr m)
                            return expr
                        Nothing   -> do
                            zoom stack (put $! path:paths)
                            expr <- runLoad
                                (fmap join (traverse loadStatic expr'))
                            zoom stack (put paths)
                            return expr )

-- | Resolve all imports within an expression
load :: Expr Path -> IO (Expr Void)
load expr = with
    (evalStateT (runLoad (fmap join (traverse loadStatic expr))) status)
    return
  where
    status = Status [] HashMap.empty Nothing
