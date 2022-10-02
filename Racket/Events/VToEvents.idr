module Racket.Events.VToEvents

import Data.Vect
import Data.Vect.Quantifiers
import Racket.Events

public export
data VToEvents : (0 n : Nat) -> (0 ls : Vect (S n) Type) -> Type where
  Nil  : {0 t, e : Type} -> {s : Type} -> (0 is : IsEvent e s) => ToEvent t e => VToEvents 0 [t]
  (::) : {0 t, e : Type} -> {s : Type} -> (0 is : IsEvent e s) => ToEvent t e -> VToEvents n ts -> VToEvents (S n) (t :: ts)

public export
vsyncs : VToEvents n ts -> Vect (S n) Type
vsyncs (Nil {s}) = [s]
vsyncs ((::) {s} to r) = s :: vsyncs r

public export
VEitherify : Vect n Type -> Type
VEitherify = foldr (flip Either) ()

public export
VSyncs : VToEvents n es -> Type
VSyncs = VEitherify . vsyncs

public export
Unionised : VToEvents n es -> Type
Unionised = AnyEvent . VSyncs

HVect : Vect n Type -> Type
HVect = All id

public export
Step : {n, m : Nat} -> {es : Vect (S n) Type} -> {es2 : Vect (S m) Type} -> VToEvents n es -> VToEvents m es2 -> Type
Step tos tos2 = (VSyncs tos2 -> VSyncs tos) -> (1 _ : HVect es2) -> Vect (S m) (Unionised tos)

-- step : (tos : VToEvents n es) => (tos2 : VToEvents m es2) -> Step tos tos2
-- step Nil f [e] = [wrapEvent f e]
-- step ((::) {s,is} to next) f (ev :: evs) = wrapEvent (f . Right) ev :: step next (f . Left) evs


-- ||| We speak together
-- export
-- unionise : (tos : ToEvents e) => (1 _ : HList e) -> List (Unionised tos)
-- unionise evs = step tos id evs
