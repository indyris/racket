module Racket.CustodianBoxes

import Ffiglet
import Racket.Custodians

export
data CustodianBox : Type -> Type where [external]

export
ToFFI (CustodianBox t) (CustodianBox t) where toFFI = id

export
FromFFI (CustodianBox t) (CustodianBox t) where fromFFI = Just

%foreign "scheme,racket:custodian-box?"
prim__isCustodianBox : AnyPtr -> Bool

export
isCustodianBox : {0 t : Type} -> t -> Bool
isCustodianBox = prim__isCustodianBox . believe_me

SafeCast (CustodianBox AnyPtr) where
  safeCast ptr = if isCustodianBox ptr then Just (believe_me ptr) else Nothing

SafeCast (CustodianBox Any) where
  safeCast ptr = if isCustodianBox ptr then Just (believe_me $ MkAny ptr) else Nothing

%foreign "scheme,racket:make-custodian-box"
prim__makeCustodianBox : AnyPtr -> AnyPtr -> PrimIO AnyPtr

export
makeCustodianBox : HasIO io => {0 t : Type} -> Custodian -> t -> io (CustodianBox t)
makeCustodianBox c v =
  pure . believe_me =<< primIO (prim__makeCustodianBox (believe_me c) (believe_me v))

%foreign "scheme,racket:custodian-box-value"
prim__custodianBoxValue : AnyPtr -> PrimIO AnyPtr

export
custodianBoxValue : HasIO io => {0 t : Type} -> CustodianBox t -> io t
custodianBoxValue b =
  pure . believe_me =<< primIO (prim__custodianBoxValue $ believe_me b)
