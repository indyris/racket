module Racket.Custodians

import Ffiglet
import Racket.Parameters

-- IsCustodian

export
interface IsCustodian (t : Type) where

-- Custodian

export
data Custodian : Type where [external]

export
IsCustodian Custodian where

export
ToFFI Custodian Custodian where toFFI = id

export
FromFFI Custodian Custodian where fromFFI = Just

-- isCustodian (SafeCast Custodion)

%foreign "scheme,racket:custodian?"
prim__isCustodian : AnyPtr -> Bool

export
isCustodian : {0 t : Type} -> t -> Bool
isCustodian = prim__isCustodian . believe_me

export
SafeCast Custodian where
  safeCast ptr = if isCustodian ptr then Just (believe_me ptr) else Nothing

-- makeCustodian'

%foreign "scheme,racket:make-custodian"
prim__makeCustodian0 : PrimIO Custodian

export
makeCustodian' : HasIO io => io Custodian
makeCustodian' = primIO prim__makeCustodian0

-- makeCustodian

%foreign "scheme,racket:make-custodian"
prim__makeCustodian1 : AnyPtr -> PrimIO Custodian

export
makeCustodian : HasIO io => t -> io Custodian
makeCustodian c = primIO $ prim__makeCustodian1 $ believe_me c

-- custodianShutdownAll

%foreign "scheme,racket:custodian-shutdown-all"
prim__custodianShutdownAll : AnyPtr -> PrimIO ()

export
custodianShutdownAll : HasIO io => Custodian -> io ()
custodianShutdownAll c = primIO $ prim__custodianShutdownAll $ believe_me c

-- isCustodianShutDown

%foreign "scheme,racket:custodian-shut-down?"
prim__isCustodianShutDown : AnyPtr -> PrimIO Bool

export
isCustodianShutDown : HasIO io => Custodian -> io Bool
isCustodianShutDown c = primIO $ prim__isCustodianShutDown (believe_me c)

-- currentCustodian

%foreign "scheme,racket:(lambda () current-custodian)"
prim__currentCustodian : PrimIO (Parameter Custodian)

export
currentCustodian : HasIO io => io (Parameter Custodian)
currentCustodian = primIO prim__currentCustodian

export
getCurrentCustodian : HasIO io => io Custodian
getCurrentCustodian = currentCustodian >>= readParameter

export
setCurrentCustodian : HasIO io => Custodian -> io ()
setCurrentCustodian e = currentCustodian >>= \f => writeParameter f e

-- custodianManagedList (TODO pending figuring out list ffi)

%foreign "scheme,racket:custodian-managed-list"
prim__custodianManagedList : AnyPtr -> AnyPtr -> PrimIO AnyPtr

-- export
-- custodianManagedList : HasIO io => a -> b -> io (List AnyPtr)
-- custodianManagedList a b = primIO $ prim__custodianManagedList (believe_me a) (believe_me b)

-- custodianMemoryAccountingAvailable

%foreign "scheme,racket:custodian-memory-accounting-available"
prim__custodianMemoryAccountingAvailable : PrimIO Bool

export
custodianMemoryAccountingAvailable : HasIO io => io Bool
custodianMemoryAccountingAvailable = primIO prim__custodianMemoryAccountingAvailable

-- custodianRequireMemory

%foreign "scheme,racket:custodian-require-memory"
prim__custodianRequireMemory : AnyPtr -> AnyPtr -> AnyPtr -> PrimIO ()

export
custodianRequireMemory : HasIO io => Custodian -> Int -> Custodian -> io ()
custodianRequireMemory c l d =
  primIO $ prim__custodianRequireMemory (believe_me c) (believe_me l) (believe_me d)

-- custodianLimitMemory'

%foreign "scheme,racket:custodian-limit-memory"
prim__custodianLimitMemory2 : AnyPtr -> AnyPtr -> PrimIO ()

export
custodianLimitMemory' : HasIO io => Custodian -> Int -> io ()
custodianLimitMemory' c l =
  primIO $ prim__custodianLimitMemory2 (believe_me c) (believe_me l)

-- custodianLimitMemory

%foreign "scheme,racket:custodian-limit-memory"
prim__custodianLimitMemory3 : AnyPtr -> AnyPtr -> AnyPtr -> PrimIO ()

export
custodianLimitMemory : HasIO io => Custodian -> Int -> Custodian -> io ()
custodianLimitMemory c l d =
  primIO $ prim__custodianLimitMemory3 (believe_me c) (believe_me l) (believe_me d)
