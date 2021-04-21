module MonadTrans

import public Control.Monad.Trans
import public Control.Monad.State

-- Classes

public export
interface Monad m => MonadIO m where
  liftIO : IO a -> m a

public export
implementation MonadIO IO where
  liftIO = id

public export
implementation MonadIO m => MonadIO (StateT s m) where
  liftIO x = ST $ \st => do
    val <- liftIO x
    pure (val, st)

public export
interface Monad m => MonadError e m | m where
  throwError : e -> m a
  catchError : m a -> (e -> m a) -> m a

public export
implementation MonadError e (Either e) where
  throwError = Left
  catchError (Left e) f = f e
  catchError (Right x) f = Right x

public export
implementation MonadError () Maybe where
  throwError () = Nothing
  catchError Nothing f = f ()
  catchError (Just x) f = Just x

public export
implementation MonadError e m => MonadError e (StateT s m) where
  throwError e = lift $ throwError e
  catchError (ST x) f = ST $ \st => catchError (x st) $ flip runStateT st . f

public export
interface Monad m => MonadReader r m | m where
  ask : m r
  local : (r -> r) -> m a -> m a
  reader : (r -> a) -> m a

-- public export
-- implementation MonadReader r ((->) r) where
--   ask = id
--   local f g = g . f
--   reader = id


-- ExceptT

public export
record ExceptT (e : Type) (m : Type -> Type) (a : Type) where
  constructor MkExceptT
  runExceptT : m (Either e a)

public export
implementation Functor m => Functor (ExceptT e m) where
  map f (MkExceptT x) = MkExceptT $ map (map f) x

public export
implementation Monad m => Applicative (ExceptT e m) where
  pure = MkExceptT . pure . pure

  (MkExceptT mf) <*> (MkExceptT mx) = MkExceptT $ do
    Right f <- mf
      | Left e => pure $ Left e
    Right x <- mx
      | Left e => pure $ Left e
    pure $ Right $ f x

public export
implementation Monad m => Monad (ExceptT e m) where
  (MkExceptT mx) >>= f = MkExceptT $ do
    Right x <- mx
      | Left e => pure $ Left e
    runExceptT $ f x

public export
implementation MonadTrans (ExceptT e) where
  lift x = MkExceptT $ map Right x

public export
implementation MonadState s m => MonadState s (ExceptT e m) where
  get = lift get
  put x = lift $ put x

public export
implementation Monad m => MonadError e (ExceptT e m) where
  throwError = MkExceptT . pure . Left
  catchError (MkExceptT mx) f = MkExceptT $ do
    Left e <- mx
      | Right x => pure $ Right x
    runExceptT $ f e

public export
implementation MonadIO m => MonadIO (ExceptT e m) where
  liftIO = MkExceptT . map Right . liftIO

public export
implementation MonadReader r m => MonadReader r (ExceptT e m) where
  ask = lift ask
  local f (MkExceptT x) = MkExceptT $ local f x
  reader = lift . reader


-- ReaderT

public export
record ReaderT (r : Type) (m : Type -> Type) (a : Type) where
  constructor MkReaderT
  runReaderT : r -> m a

public export
implementation Functor m => Functor (ReaderT r m) where
  map f (MkReaderT g) = MkReaderT $ map f . g

public export
implementation Applicative m => Applicative (ReaderT r m) where
  pure = MkReaderT . const . pure
  MkReaderT f <*> MkReaderT x = MkReaderT $ \r => f r <*> x r

public export
implementation Monad m => Monad (ReaderT r m) where
  MkReaderT x >>= f = MkReaderT $ \r => x r >>= flip runReaderT r . f

public export
implementation MonadTrans (ReaderT r) where
  lift = MkReaderT . const

public export
implementation Monad m => MonadReader r (ReaderT r m) where
  ask = MkReaderT pure
  local f (MkReaderT x) = MkReaderT $ x . f
  reader f = MkReaderT $ pure . f

public export
implementation MonadState s m => MonadState s (ReaderT r m) where
  get = MkReaderT $ const get
  put = MkReaderT . const . put

public export
implementation MonadError e m => MonadError e (ReaderT r m) where
  throwError = MkReaderT . const . throwError
  catchError (MkReaderT a) h = MkReaderT $ \r => catchError (a r) (flip runReaderT r . h)

public export
implementation MonadIO m => MonadIO (ReaderT r m) where
  liftIO = MkReaderT . const . liftIO
