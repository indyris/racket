module Racket.Pairs

import Ffiglet
import Data.Vect
import Racket.Pairs.Prim

export
isCons : t -> Bool
isCons = prim__isPair . believe_me

export
isNull : t -> Bool
isNull = prim__isNull . believe_me

export
data Null : Type where [external]

export
null : Null
null = believe_me prim__null

export
data Cons : Type -> Type -> Type where [external]

export
cons : t -> u -> Cons t u
cons car cdr = believe_me $ prim__cons (believe_me car) (believe_me cdr)

export
cons' : t -> u -> Cons AnyPtr AnyPtr
cons' car cdr = believe_me $ prim__cons (believe_me car) (believe_me cdr)

export
cons'' : t -> u -> AnyPtr
cons'' car cdr = believe_me $ prim__cons (believe_me car) (believe_me cdr)

export
SafeCast (Cons AnyPtr AnyPtr) where
  safeCast ptr = if isCons ptr then Just (believe_me ptr) else Nothing

export
car : {0 t,u : Type} -> Cons t u -> t
car = believe_me . prim__car . believe_me

export
cdr : Cons t u -> u
cdr = believe_me . prim__cdr . believe_me

export
cadr : {0 a, b, c : Type} -> Cons a (Cons b c) -> b
cadr = car . cdr

export
cddr : {0 a, b, c : Type} -> Cons a (Cons b c) -> c
cddr = cdr . cdr

export
caddr : {0 a, b, c, d : Type} -> Cons a (Cons b (Cons c d)) -> c
caddr = car . cddr

export
cdddr : {0 a, b, c, d : Type} -> Cons a (Cons b (Cons c d)) -> d
cdddr = cdr . cddr

export
cadddr : {0 a, b, c, d, e : Type} -> Cons a (Cons b (Cons c (Cons d e))) -> d
cadddr = caddr . cdr

export
cddddr : {0 a, b, c, d, e : Type} -> Cons a (Cons b (Cons c (Cons d e))) -> e
cddddr = cdr . cdddr

-- HConses

||| A neater way of writing nested Cons.
public export
HConses : (1 _ : List Type) -> Type
HConses Nil = Null
HConses (h :: hs) = Cons h (HConses hs)

-- hlistType : List Type -> Type
-- hlistType t = hlt t where
--   hlt : List Type -> Type
--   hlt Nil = HList t
--   hlt (a :: b) = a -> hlt b

-- hlist : hlistType ts
-- hlist = ?help

||| length-indexed HConses
public export
HVect : (0 n : Nat) -> (1 _ : Vect n Type) -> Type
HVect Z Nil = Null
HVect (S n) (a :: b) = Cons a (HVect n b)

-- hVectType : (ts : Vect n Type) -> Type
-- hVectType ts = hv ts where
--   hv : (1 v : Vect m Type) -> Type
--   hv Nil = HVect n ts
--   hv (a :: b) = a -> hv b

-- hvect : {n : Nat} -> (ts : Vect n Type) -> HVect n ts
-- hvect Nil = null
-- hvect (a :: b) = ?help2 where
--   compose : {m : Nat} -> {ts' : Vect m Type} -> hVectType ts'
--   compose {m=Z} = null
--   compose {m=S m} = compose $ \a => cons a . compose {m=m}

