module Racket.Lists

import Ffiglet
import Data.Vect
import Racket.Pairs
import Racket.Pairs.Prim

%default total

||| Represents a native scheme list containing one type
export
data Conses : Type -> Type where [external]

export
null : Conses t
null = believe_me prim__null

export
cons : t -> Conses t -> Conses t
cons v = believe_me . prim__cons (believe_me v) . believe_me

export
pure : t -> Conses t
pure = (flip cons) null

export
toCons : Conses t -> Either Null (Cons t (Conses t))
toCons c = 
let c = believe_me c in believe_me $
  if prim__isPair c then Right $ prim__car c else Left prim__null

export
fromList : List t -> Conses t
fromList Nil = null
fromList (a :: b) = cons a $ fromList b

export
fromVect : Vect n t -> Conses t
fromVect Nil = null
fromVect (a :: b) = cons a $ fromVect b

export
toList : Conses t -> List t
toList c = case toCons c of
  Left _ => Nil
  Right c => assert_total $ car c :: toList (cdr c)

export
car : Conses t -> Maybe t
car c = let c = believe_me c in believe_me $
  if prim__isPair c then Just $ prim__car c else Nothing

export
cdr : Conses t -> Maybe (Conses t)
cdr c = let c = believe_me c in believe_me $
  if prim__isPair c then Just $ prim__cdr c else Nothing

export
Semigroup (Conses t) where
  (<+>) a = believe_me . prim__append (believe_me a) . believe_me

export
Functor Conses where
  map f = believe_me . prim__map (believe_me f) . believe_me

export
Applicative Conses where
  pure = Racket.Lists.pure
  (<*>) fs as = believe_me $ prim__appendStar $
   prim__zipWith (believe_me ap) (believe_me fs) (believe_me as) where
     ap : (a -> b) -> a -> b
     ap a = a

export
Monad Conses where
  (>>=) a f = believe_me $ prim__appendMap (believe_me f) (believe_me a)
  join = believe_me . prim__appendStar . believe_me

-- export
-- cartesianProduct : (Conses a) -> (Conses b) -> Conses (HList [a,b])
-- cartesianProduct a = believe_me . prim__cartesianProduct2 (believe_me a) . believe_me
