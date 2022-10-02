module Racket.Events

import Data.Fin
import Data.Either
import Data.Nat
import Data.Nat.Order
import Data.List.Elem
import public Data.List.Quantifiers
import Data.Vect
import Data.Vect.Quantifiers
import Ffiglet
import Racket.Pairs
import Racket.Lists
import Racket.Time
import Racket.Util

public export
interface IsEvent (0 e : Type) (0 sync : Type) | e where

public export
interface IsEvent e s => ToEvent (0 t : Type) (0 e : Type) (0 s : Type) | t where
  toEvent : t -> e

public export
IsEvent e s => ToEvent e e s where
  toEvent = id

public export
ToEvent2 : Type -> Type -> Type
ToEvent2 e s = ToEvent e e s

public export
ToEvent1 : Type -> Type
ToEvent1 e = ToEvent2 e e

||| A type-erased event that synchronises with a particular result type
export
data AnyEvent : Type -> Type where [external]

export
IsEvent (AnyEvent a) a where

-- Helper to let us write the next instance
export %inline
toAnyEvent : ToEvent t e s => t -> AnyEvent s
toAnyEvent = believe_me . toEvent

-- export
%foreign "scheme,racket:evt?"
isEvent : a -> Bool

%foreign "scheme,racket:wrap-evt"
prim__wrapEvent : a -> (e -> e2) -> AnyEvent e2

export %inline
wrapEvent : (to : ToEvent t e s) => (s -> s2) -> t -> AnyEvent s2
wrapEvent f ev = prim__wrapEvent (toEvent ev) f

export %inline
replaceEvent : ToEvent t e s => s2 -> t -> AnyEvent s2
replaceEvent r = wrapEvent (const r)

export
data AlarmEvent : Type where [external]

export
IsEvent AlarmEvent AlarmEvent where

%foreign "scheme,racket:alarm-evt"
prim__alarmEvent : Double -> Bool -> AlarmEvent

export %inline
alarmEvent : Double -> Bool -> AlarmEvent
alarmEvent = prim__alarmEvent

export
alarmIn : HasIO io => Double -> io AlarmEvent
alarmIn delay = do
  now <- currentInexactMonotonicMilliseconds
  pure $ alarmEvent (now + delay) True

public export
data ToEvents : (0 ts : List Type) -> Type where
  Nil  : {0 t, e : Type} -> {s : Type} -> (to : ToEvent t e s) => ToEvents [t]
  (::) : {0 t, e : Type} -> {s : Type} -> (to : ToEvent t e s) -> ToEvents ts -> ToEvents (t :: ts)

export
Uninhabited (ToEvents Nil) where
  uninhabited Nil impossible
  uninhabited (_ :: _) impossible

public export
syncs : ToEvents ts -> List Type
syncs (Nil {s}) = [s]
syncs ((::) {s} to r) = s :: syncs r

public export
Eitherify : Type -> List Type -> Type
Eitherify nil = foldr (flip Either) nil

public export
Syncs : ToEvents es -> Type
Syncs = Eitherify () . syncs

public export
Unionised : ToEvents es -> Type
Unionised es = AnyEvent (Syncs es)

-- Rest of the type of `step`
Step : {es2 : List Type} -> (tos : ToEvents es) -> (tos2 : ToEvents es2) -> Type
Step tos tos2 = (Syncs tos2 -> Syncs tos) -> (1 _ : HList es2) -> List (Unionised tos)

step : (0 tos : ToEvents es) => (1 tos2 : ToEvents es2) -> Step tos tos2
step (Nil {to}) f [e] = [wrapEvent {to} (f . Right) e]
step (to :: n) f (ev :: evs) = wrapEvent (f . Right) ev :: step n (f . Left) evs

||| We speak together
export
unionise : (1 tos : ToEvents e) => (1 _ : HList e) -> List (Unionised tos)
unionise evs = step tos id evs

%foreign "scheme,racket:(lambda (es) (apply sync es))"
prim__sync : a -> PrimIO b

export
sync : HasIO io => (tos : ToEvents es) => HList es -> io (Syncs tos)
sync events = primIO (prim__sync evs) where
  evs : Conses (Unionised tos)
  evs = fromList (unionise events)  

%foreign "scheme,racket:sync"
prim__sync1 : a -> PrimIO b

export
sync1 : HasIO io => ToEvent t e s => t -> io s
sync1 t = primIO (prim__sync1 (toEvent t))

%foreign "scheme,racket:sync"
prim__sync2 : a -> b -> PrimIO c

export
sync2
  :  HasIO io
  => ToEvent t1 e1 s1
  => ToEvent t2 e2 s2
  => t1
  -> t2
  -> io (Either s1 s2)
sync2 e1 e2 = primIO (prim__sync2 e1' e2') where
  e1', e2' : AnyEvent (Either s1 s2)
  e1' = wrapEvent Left e1
  e2' = wrapEvent Right e2

%foreign "scheme,racket:sync"
prim__sync3 : a -> b -> c -> PrimIO d

export
sync3
  :  HasIO io
  => ToEvent t1 e1 s1
  => ToEvent t2 e2 s2
  => ToEvent t3 e3 s3
  => t1
  -> t2
  -> t3
  -> io (Either (Either s1 s2) s3)
sync3 e1 e2 e3 = primIO (prim__sync3 e1' e2' e3') where
  e1', e2', e3' : AnyEvent (Either (Either s1 s2) s3)
  e1' = wrapEvent (Left . Left) e1
  e2' = wrapEvent (Left . Right) e2
  e3' = wrapEvent Right e3

%foreign "scheme,racket:sync"
prim__sync4 : a -> b -> c -> d -> PrimIO e

export
sync4
  :  HasIO io
  => ToEvent t1 e1 s1
  => ToEvent t2 e2 s2
  => ToEvent t3 e3 s3
  => ToEvent t4 e4 s4
  => t1
  -> t2
  -> t3
  -> t4
  -> io (Either (Either (Either s1 s2) s3) s4)
sync4 e1 e2 e3 e4 = primIO (prim__sync4 e1' e2' e3' e4') where
  e1', e2', e3', e4' : AnyEvent (Either (Either (Either s1 s2) s3) s4)
  e1' = wrapEvent (Left . Left . Left) e1
  e2' = wrapEvent (Left . Left . Right) e2
  e3' = wrapEvent (Left . Right) e3
  e4' = wrapEvent Right e4

%foreign "scheme,racket:sync"
prim__sync5 : a -> b -> c -> d -> e -> PrimIO f

export
sync5
  :  HasIO io
  => ToEvent t1 e1 s1
  => ToEvent t2 e2 s2
  => ToEvent t3 e3 s3
  => ToEvent t4 e4 s4
  => ToEvent t5 e5 s5
  => t1
  -> t2
  -> t3
  -> t4
  -> t5
  -> io (Either (Either (Either (Either s1 s2) s3) s4) s5)
sync5 e1 e2 e3 e4 e5 = primIO (prim__sync5 e1' e2' e3' e4' e5') where
  e1', e2', e3', e4', e5' : AnyEvent (Either (Either (Either (Either s1 s2) s3) s4) s5)
  e1' = wrapEvent (Left . Left . Left . Left) e1
  e2' = wrapEvent (Left . Left . Left . Right) e2
  e3' = wrapEvent (Left . Left . Right) e3
  e4' = wrapEvent (Left . Right) e4
  e5' = wrapEvent Right e5

export
data ChoiceEvent : (0 _ : ToEvents es) -> Type where [external]

export
IsEvent (ChoiceEvent es) (Unionised es) where

%foreign "scheme,racket:(lambda (es) (apply choice-evt es))"
prim__choiceEvent : a -> ChoiceEvent es

export
choiceEvent
  :  HasIO io
  => (tos : ToEvents es)
  => HList es
  -> ChoiceEvent events
choiceEvent events = prim__choiceEvent (Racket.Lists.fromList $ unionise events)

-- this is stuff for implementing syncFor...

-- StepWith : {es2 : List Type} -> (Type -> Type) -> ToEvents es -> ToEvents es2 -> Type
-- StepWith f tos tos2 =
--   (f (Syncs tos2) -> f (Syncs tos)) -> (1 _ : HList es2) -> List (AnyEvent (f (Syncs tos)))

-- stepWith
--   :  (0 f : Type -> Type)
--   -> (Sync es -> Sync es)
--   -> (0 tos1 : ToEvents es)
--   => (1 tos2 : ToEvents es2)
--   -> StepWith f tos1 tos2
-- stepWith _ Nil f [e] = [wrapEvent f e]
-- stepWith _ (to :: n) f (ev :: evs) = wrapEvent (f . Right) ev :: step n (f . Left) evs
-- public export
-- MUnionised : ToEvents es -> Type
-- MUnionised es = AnyEvent (Maybe (Syncs es))

-- public export
-- MStep : {es2 : List Type} -> ToEvents es -> ToEvents es2 -> Type
-- MStep tos tos2 = (Maybe (Syncs tos2) -> Maybe (Syncs tos)) -> (1 _ : HList es2) -> List (MUnionised tos)

-- mstep : (tos : ToEvents es) => (tos2 : ToEvents es2) -> MStep tos tos2
-- mstep Nil f [e] = [wrapEvent f e]
-- mstep (to :: n) f (ev :: evs) = wrapEvent (map $ f . Right) ev :: step n (map $ f . Left) evs

-- ||| We speak together
-- export
-- munionise : (tos : ToEvents e) => (_ : HList e) -> List (MUnionised tos)
-- munionise evs = step tos Just evs

-- %foreign "scheme,racket:sync/timeout"
-- prim__syncFor : Double -> a -> PrimIO b

-- export
-- syncFor : HasIO io => (tos : ToEvents es) => Double -> HList es -> io (Maybe $ Unionised tos)
-- syncFor t e = unfalsifiable <$> primIO (prim__syncFor t e)


-- %foreign "scheme,racket:sync/timeout"
-- prim__syncFor1 : Double -> a -> PrimIO b

-- export
-- syncFor1 : HasIO io => (e' : IsEvent e) => Double -> e -> io (Maybe $ syncResult @{e'})
-- syncFor1 t e = unfalsifiable <$> primIO (prim__syncFor1 t e)

-- %foreign "scheme,racket:sync/timeout"
-- prim__syncFor2 : Double -> a -> b -> PrimIO c

-- export
-- syncFor2
--   :  HasIO io
--   => (i1 : IsEvent e1)
--   => (i2 : IsEvent e2)
--   => Double
--   -> e1
--   -> e2
--   -> io (Maybe $ Either (syncResult @{i1}) (syncResult @{i2}))
-- syncFor2 t e1 e2 = unfalsifiable <$> primIO (prim__syncFor2 t e1' e2') where
--   e1', e2' : AnyEvent (Either (syncResult @{i1}) (syncResult @{i2}))
--   e1' = wrapEvent Left e1
--   e2' = wrapEvent Right e2

-- %foreign "scheme,racket:sync/timeout"
-- prim__syncFor3 : Double -> a -> b -> c -> PrimIO d

-- export
-- syncFor3
--   :  HasIO io
--   => (i1 : IsEvent e1)
--   => (i2 : IsEvent e2)
--   => (i3 : IsEvent e3)
--   => Double
--   -> e1
--   -> e2
--   -> e3
--   -> io (Maybe $ Either (Either (syncResult @{i1}) (syncResult @{i2})) (syncResult @{i3}))
-- syncFor3 t e1 e2 e3 = unfalsifiable <$> primIO (prim__syncFor3 t e1' e2' e3') where
--   e1', e2', e3' : AnyEvent (Either (Either (syncResult @{i1}) (syncResult @{i2})) (syncResult @{i3}))
--   e1' = wrapEvent (Left . Left) e1
--   e2' = wrapEvent (Left . Right) e2
--   e3' = wrapEvent Right e3

-- %foreign "scheme,racket:sync"
-- prim__sync4 : a -> b -> c -> d -> PrimIO e

-- %foreign "scheme,racket:sync"
-- prim__sync5 : a -> b -> c -> d -> e -> PrimIO f

-- this all doesn't work out very well. giving up for now

-- this mess never really worked and was difficult to write and let's forget about it for now.


-- export
-- sync
--   :  HasIO io
--   => {n : Nat}
--   -> (es : Vect (S n) Type)
--   => (as : AreToEvents es)
--   => HVect es
--   -> io (eSyncResult es as)
-- sync events = primIO (prim__sync evs) where
--   evs : Conses (Unionised es as)
--   evs = fromVect (unionise {n=S n} events)  

-- %foreign "scheme,racket:(lambda (timeout es) (apply sync/timeout timeout es))"
-- prim__syncTimeout : Double -> AnyPtr -> PrimIO AnyPtr

-- export
-- syncFor
--   :  HasIO io
--   => (n : Nat)
--   => (es : Vect (S n) Type)
--   => (as : AreToEvents es)
--   => Double
--   -> HVect es
--   -> io (Maybe . Eitherify $ syncResults es as)
-- syncFor timeout events = unfalsifiable . believe_me <$>
--   primIO (prim__syncTimeout timeout $ believe_me evs) where
--     evs : Conses (Unionised es as)
--     evs = fromVect (unionise {n=S n} events)  

-- simpleTest : HasIO io => (e : AlarmEvent) -> (f : AlarmEvent) -> io (esyncResult [AlarmEvent,AlarmEvent] [e,f])
-- simpleTest e f = sync [e, f]
