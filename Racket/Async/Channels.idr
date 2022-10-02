module Racket.Async.Channels

import Racket.Events
import Racket.Util

export
%foreign "scheme,racket:async-channel?"
isAsyncChannel : AnyPtr -> Bool

export
data Channel : (0 send : Type) -> (0 receive : Type) -> Type where [external]

export
data Sender : (0 msg : Type) -> Type where [external]

export
data Receiver : (0 msg : Type) -> Type where [external]

export
IsEvent (Channel send receive) receive where

export
IsEvent (Receiver msg) msg where

export
splitChannel : Channel s r -> (Sender s, Receiver r)
splitChannel c = (believe_me c, believe_me c)

public export
interface ToSender (0 s : Type) (0 m : Type) | s where
  toSender : s -> Sender m

export
ToSender (Channel s r) s where toSender = believe_me

public export
ToSender (Sender m) m where toSender = id

public export
interface ToReceiver (0 r : Type) (0 m : Type) | r where
  toReceiver : r -> Receiver m

export
ToReceiver (Channel s r) r where toReceiver = believe_me

public export
ToReceiver (Receiver m) m where toReceiver = id

public export
RToEvent : Type -> Type
RToEvent msg = ToEvent2 (Receiver msg) msg

%foreign "scheme,racket:make-async-channel"
prim__asyncChannel0 : PrimIO (Channel s r)
export
unboundedAsyncChannel : HasIO io => io (Channel s r)
unboundedAsyncChannel = primIO prim__asyncChannel0

%foreign "scheme,racket:make-async-channel"
prim__asyncChannel1 : Int -> PrimIO (Channel s r)

export
boundedAsyncChannel : HasIO io => Int -> io (Channel s r)
boundedAsyncChannel limit = primIO $ prim__asyncChannel1 limit

%foreign "scheme,racket:async-channel-get"
prim__asyncChannelGet : a -> PrimIO b

export
asyncChannelGet : HasIO io => (to : ToReceiver c m) => c -> io m
asyncChannelGet chan = primIO $ prim__asyncChannelGet (toReceiver @{to} chan)

%foreign "scheme,racket:async-channel-try-get"
prim__asyncChannelTryGet : a -> PrimIO (Falsifiable b)

export
asyncChannelTryGet : HasIO io => (to : ToReceiver c m) => c -> io (Falsifiable m)
asyncChannelTryGet chan = primIO $ prim__asyncChannelTryGet (toReceiver @{to} chan)

%foreign "scheme,racket:async-channel-put"
prim__asyncChannelPut : c -> s -> PrimIO ()

export
asyncChannelPut : (to : ToSender c m) => HasIO io => m -> c -> io ()
asyncChannelPut v chan = primIO $ prim__asyncChannelPut (toSender @{to} chan) v

-- this is slightly more tedious than it looks
-- data AsyncChannelPutEvent : Channel s r -> Type where [external]
  
-- %foreign "scheme,racket:async-channel-put-evt"
-- prim__asyncChannelPutEvent : Channel s r -> s -> PrimIO t

-- export
-- asyncChannelPutEvent : HasIO io => Channel t -> io t
-- asyncChannelPutEvent v chan = primIO $ prim__asyncChannelPut chan v

