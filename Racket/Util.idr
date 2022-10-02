module Racket.Util

import Control.Monad.Either
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Writer
import public Control.Monad.Either
import Data.Maybe
import Data.List.Quantifiers
import Ffiglet
import Racket.Basics

%default total

-- Data.List.Quantifiers

export
zipAllWith : ((theA : a) -> p theA -> b) -> (as : List a) -> All p as -> List b
zipAllWith f Nil Nil = Nil
zipAllWith f (theA :: theAs) (theP :: thePs) = f theA theP :: zipAllWith f theAs thePs

-- Falsifiable

export
data Falsifiable : Type -> Type where [external]

export %inline
falsifiable : a -> Falsifiable a
falsifiable = believe_me

export %inline
unfalsifiable : Falsifiable a -> Maybe a
unfalsifiable a = if isFalse a then Nothing else Just $ believe_me a

export %inline
doubleToBool : Double -> Bool
doubleToBool d = d /= 0.0

-- %foreign "javascript:lambda:(a,b)=>a === b?1:0"
-- prim__eqv : AnyPtr -> AnyPtr -> Double

-- ||| Heterogeneous pointer equality. This calls the Javascript
-- ||| `===` operator internally.
-- export
-- eqv : a -> b -> Bool
-- eqv x y = doubleToBool $ prim__eqv (believe_me x) (believe_me y)

-- %foreign "javascript:lambda:x=>String(x)"
-- prim__show : AnyPtr -> String

-- ||| Displays a JS value by passing it to `String(...)`.
-- export
-- rackShow : a -> String
-- rackShow v = prim__show (believe_me v)

--------------------------------------------------------------------------------
--          IO
--------------------------------------------------------------------------------

-- %foreign "scheme,racket:println"
-- prim__consoleLog : String -> PrimIO ()

-- export
-- consoleLog : HasIO io => String -> io ()
-- consoleLog s = primIO $ prim__consoleLog s

-- public export
-- data RackErr : Type where
--   Caught    : (msg : String) -> RackErr
--   CastErr   : (inFunction : String) -> (value : a) -> RackErr
--   IsNothing : (callSite : String) -> RackErr

-- export
-- dispErr : RackErr -> String
-- dispErr (CastErr inFunction value) = #"""
--   Error when casting a Racket value in function \#{inFunction}.
--     The value was: \#{rackShow value}.
--     The value's type was \#{typeof value}.
--   """#

-- dispErr (IsNothing callSite) =
--   #"Trying to extract a value from Nothing at \#{callSite}"#

-- dispErr (Caught msg) = msg


-- public export
-- RackIO : Type -> Type
-- RackIO = EitherT RackErr IO

-- public export
-- interface HasIO io => LiftRackIO io where
--   liftRackIO : RackIO a -> io a

-- export %inline
-- LiftRackIO RackIO where
--   liftRackIO = id

-- export %inline
-- LiftRackIO m => LiftRackIO (StateT s m) where
--   liftRackIO m = ST $ \st => (st,) <$> liftRackIO m

-- export %inline
-- LiftRackIO m => LiftRackIO (ReaderT e m) where
--   liftRackIO m = MkReaderT $ \_ => liftRackIO m

-- export %inline
-- LiftRackIO m => LiftRackIO (WriterT w m) where
--   liftRackIO m = MkWriterT $ \vw => (,vw) <$> liftRackIO m

-- export %inline
-- LiftRackIO m => LiftRackIO (RWST r w w m) where
--   liftRackIO m = MkRWST $ \_,vs,vw => (,vs,vw) <$> liftRackIO m

-- export
-- runRackWith : Lazy (RackErr -> IO a) -> RackIO a -> IO a
-- runRackWith f (MkEitherT io) = io >>= either f pure

-- export
-- runRack : RackIO () -> IO ()
-- runRack = runRackWith (consoleLog . dispErr)

-- export
-- runRackWithDefault : Lazy a -> RackIO a -> IO a
-- runRackWithDefault a = runRackWith (\e => consoleLog (dispErr e) $> a)

-- export %inline
-- primRack : PrimIO a -> RackIO a
-- primRack = primIO

-- export
-- unMaybe : (callSite : String) -> RackIO (Maybe a) -> RackIO a
-- unMaybe callSite io = do Just a <- io
--                            | Nothing => throwError $ IsNothing callSite
--                          pure a

-- --------------------------------------------------------------------------------
-- --          Error handling
-- --------------------------------------------------------------------------------

-- %foreign "javascript:lambda:(u,io) => {try { return [1,io()]; } catch (e) { return [0,String(e)] }}"
-- prim__tryIO : forall a . IO a -> PrimIO AnyPtr

-- %foreign "javascript:lambda:(x,y,f,v) => {try { return [1,f(v)]; } catch (e) { return [0,String(e)] }}"
-- prim__try : forall a,b . (a -> b) -> a -> AnyPtr

-- %foreign "javascript:lambda:x => x[0]"
-- prim__errTag : AnyPtr -> Double

-- %foreign "javascript:lambda:x => x[1]"
-- prim__errVal : AnyPtr -> AnyPtr

-- toEither : AnyPtr -> Either RackErr a
-- toEither ptr = if 1 == prim__errTag ptr
--                   then Right (believe_me (prim__errVal ptr))
--                   else Left $ Caught (believe_me (prim__errVal ptr))

-- ||| Tries to execute an IO action, wrapping any runtime exception
-- ||| in its stringified version in a `Left . Caught`.
-- export
-- tryIO : IO a -> RackIO a
-- tryIO io = do ptr <- primIO $ prim__tryIO io
--               if 1 == prim__errTag ptr
--                  then pure (believe_me (prim__errVal ptr))
--                  else throwError $ Caught (believe_me (prim__errVal ptr))

-- ||| Error handling in pure functions. This should only be used
-- ||| in foreign function calls that might fail but or otherwise
-- ||| pure calculations.
-- export
-- try : (a -> b) -> a -> Either RackErr b
-- try f a = toEither $ prim__try f a

-- export
-- tryFromFFI : FromFFI a ffiRepr => (fun : Lazy String) -> ffiRepr -> RackIO a
-- tryFromFFI fun ptr =
--   case fromFFI ptr of
--     Just v  => pure v
--     Nothing => throwError $ CastErr fun ptr

-- export
-- tryRack : FromFFI a ffiRepr => (fun : Lazy String) -> PrimIO ffiRepr -> RackIO a
-- tryRack fun prim = primIO prim >>= tryFromFFI fun
