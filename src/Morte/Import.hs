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
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Text.Lazy as Text
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

import Morte.Core (Expr, Path(..))
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

loadRaw :: Path -> Load (Expr Path)
loadRaw (File file) = do
    txt <- liftIO (Filesystem.readTextFile file)
    case exprFromText (Text.fromStrict txt) of
        Left  err  -> liftIO (throwIO err)
        Right expr -> return expr 
loadRaw (URL  url ) = do
    request  <- liftIO (HTTP.parseUrl (Text.unpack url))
    m        <- needManager
    response <- liftIO (HTTP.httpLbs request m)
    case decodeOrFail (HTTP.responseBody response) of
        Left  (_, _, err ) -> liftIO (throwIO (userError err))
        Right (_, _, expr) -> return expr

loadAll :: Path -> Load (Expr Void)
loadAll path = Load (do
    paths <- zoom stack get
    if path `elem` paths
        then liftIO (throwIO (ImportError paths path))
        else do
            m <- zoom cache get
            case HashMap.lookup path m of
                Just expr -> return expr
                Nothing   -> do
                    expr' <- runLoad (loadRaw path)
                    case traverse (\_ -> Nothing) expr' of
                        Just expr -> do
                            zoom cache (put $! HashMap.insert path expr m)
                            return expr
                        Nothing   -> do
                            zoom stack (put $! path:paths)
                            expr <- runLoad (fmap join (traverse loadAll expr'))
                            zoom stack (put paths)
                            return expr )

load :: Expr Path -> IO (Expr Void)
load expr = with
    (evalStateT (runLoad (fmap join (traverse loadAll expr))) status)
    return
  where
    status = Status [] HashMap.empty Nothing
