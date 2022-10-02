module Racket.Parameters

import Ffiglet
import Racket.Procedures

export
data Parameter : Type -> Type where [external]

export
ToFFI (Parameter t) (Parameter t) where toFFI = id

export
FromFFI (Parameter t) (Parameter t) where fromFFI = Just

%foreign "scheme,racket:parameter?"
prim__isParameter : AnyPtr -> Bool

export
isParameter : t -> Bool
isParameter = prim__isParameter . believe_me

export
readParameter : HasIO io => Parameter t -> io t
readParameter = unsafeCall0

export
writeParameter : HasIO io => Parameter t -> t -> io ()
writeParameter = unsafeCall1

export
SafeCast (Parameter AnyPtr) where
    safeCast ptr = if isParameter ptr then Just (believe_me ptr) else Nothing

-- wrapping racket parameterize generically turns out to be a bit difficult. we take advantage of the way monads work
-- and the way parameters work to just set and unset instead. this *should* be equivalent.
||| Rebinds a parameter for the duration of an action
export
withParameter : HasIO io => Parameter p -> p -> io r -> io r
withParameter p new expr = do
  old <- readParameter p
  writeParameter p new
  expr <* writeParameter p old
