module Racket.Exceptions

import Control.Function
import Decidable.Equality

import Ffiglet



interface Gendered (g : Type) where

-- data Isa : Type -> Type

-- data IsIndeedA

interface Dom (top : Type) (bot : Type) where

data Polycule : Type -> Type where
  Top : Polycule top
  Bot : Polycule top -> Polycule bot

interface Poly t where
  polycule : Polycule t

Uninhabited (Top = Bot p) where
  uninhabited Refl impossible

Uninhabited (Bot p = Top) where
  uninhabited Refl impossible

Injective (Bot {top} {bot}) where
  injective Refl = Refl

DecEq (Polycule t) where
  decEq Top Top = Yes Refl
  decEq (Bot this) (Bot that) = Yes $ believe_me True -- decEqCong $ decEq this that
  decEq Top (Bot _) = No absurd
  decEq (Bot _) Top = No absurd
-- Eq t => Eq (Polycule t) where
--   (==) Top Top = ?sdfjsd
--   (==) a b = ?sdfjsd
--   (/=) a b = ?sdfjsdsdfsd

  -- data RealPolycule : Type where
  --   IsInPolycule : RealPolycule top bot

 


-- ancestors : 
-- (bot : Type) => Is bot => Sub (super {t=bot}) bot where

%foreign "scheme,racket:(lambda (pred left right fn) (with-handlers ([pred left]) (right (fn))))"
prim__defang
  :  (pred  : AnyPtr -> Bool)
  -> (left  : AnyPtr -> Either AnyPtr AnyPtr)
  -> (right : AnyPtr -> Either AnyPtr AnyPtr)
  -> (prim  : PrimIO AnyPtr)
  -> PrimIO (Either AnyPtr AnyPtr)

export
defang : HasIO io => (pred : AnyPtr -> Bool) -> (prim : PrimIO AnyPtr) -> io (Either t e)
defang pred prim = believe_me <$> primIO (prim__defang pred Left Right prim)

public export
interface IsExn (e : Type) where

%foreign "scheme,racket:exn?"
prim__isExn : AnyPtr -> Bool

export
isExn : t -> Bool
isExn = prim__isExn . believe_me

public export
interface IsExn e => IsExnFail (e : Type) where

%foreign "scheme,racket:exn:fail?"
prim__isExnFail : AnyPtr -> Bool

export
isExnFail : t -> Bool
isExnFail = prim__isExnFail . believe_me

export
data ExnFail : Type where [external]

export
IsExn ExnFail where

export
IsExnFail ExnFail where

export
interface IsExnFail e => IsExnFailContract (e : Type) where

%foreign "scheme,racket:exn:fail:contract?"
prim__isExnFailContract : AnyPtr -> Bool

export
isExnFailContract : t -> Bool
isExnFailContract = prim__isExnFailContract . believe_me

export
data ExnFailContract : Type where [external]

export
IsExn ExnFailContract where

export
IsExnFail ExnFailContract where

export
IsExnFailContract ExnFailContract where

-- exn:fail:contract:arity

public export
interface IsExnFailContract e => IsExnFailContractArity (e : Type) where

%foreign "scheme,racket:exn:fail:contract?"
prim__isExnFailContractArity : AnyPtr -> Bool

export
isExnFailContractArity : t -> Bool
isExnFailContractArity = prim__isExnFailContractArity . believe_me

export
data ExnFailContractArity : Type where [external]

export
IsExn ExnFailContractArity where

export
IsExnFail ExnFailContractArity where

export
IsExnFailContract ExnFailContractArity where

export
IsExnFailContractArity ExnFailContractArity where

-- exn:fail:contract:divide-by-zero

public export
interface IsExnFailContract e => IsExnFailContractDivideByZero (e : Type) where

%foreign "scheme,racket:exn:fail:contract:divide-by-zero?"
prim__isExnFailContractDivideByZero : AnyPtr -> Bool

export
isExnFailContractDivideByZero : t -> Bool
isExnFailContractDivideByZero = prim__isExnFailContractDivideByZero . believe_me

export
data ExnFailContractDivideByZero : Type where [external]

export
IsExn ExnFailContractDivideByZero where

export
IsExnFail ExnFailContractDivideByZero where

export
IsExnFailContract ExnFailContractDivideByZero where

export
IsExnFailContractDivideByZero ExnFailContractDivideByZero where

-- exn:fail:contract:non-fixnum-result

public export
interface IsExnFailContract e => IsExnFailContractNonFixnumResult (e : Type) where

%foreign "scheme,racket:exn:fail:contract:non-fixnum-result?"
prim__isExnFailContractNonFixnumResult : AnyPtr -> Bool

export
isExnFailContractNonFixnumResult : t -> Bool
isExnFailContractNonFixnumResult = prim__isExnFailContractNonFixnumResult . believe_me

export
data ExnFailContractNonFixnumResult : Type where [external]

export
IsExn ExnFailContractNonFixnumResult where

export
IsExnFail ExnFailContractNonFixnumResult where

export
IsExnFailContract ExnFailContractNonFixnumResult where

export
IsExnFailContractNonFixnumResult ExnFailContractNonFixnumResult where

-- exn:fail:contract:continuation

public export
interface IsExnFailContract e => IsExnFailContractContinuation (e : Type) where

%foreign "scheme,racket:exn:fail:contract:continuation?"
prim__isExnFailContractContinuation : AnyPtr -> Bool

export
isExnFailContractContinuation : t -> Bool
isExnFailContractContinuation = prim__isExnFailContractContinuation . believe_me

export
data ExnFailContractContinuation : Type where [external]

export
IsExn ExnFailContractContinuation where

export
IsExnFail ExnFailContractContinuation where

export
IsExnFailContract ExnFailContractContinuation where

export
IsExnFailContractContinuation ExnFailContractContinuation where

-- exn:fail:contract:variable

public export
interface IsExnFailContract e => IsExnFailContractVariable (e : Type) where

%foreign "scheme,racket:exn:fail:contract:variablt?"
prim__isExnFailContractVariable : AnyPtr -> Bool

export
isExnFailContractVariable : t -> Bool
isExnFailContractVariable = prim__isExnFailContractVariable . believe_me

export
data ExnFailContractVariable : Type where [external]

export
IsExn ExnFailContractVariable where

export
IsExnFail ExnFailContractVariable where

export
IsExnFailContract ExnFailContractVariable where

export
IsExnFailContractVariable ExnFailContractVariable where

-- exn:fail:syntax

public export
interface IsExnFail e => IsExnFailSyntax (e : Type) where

%foreign "scheme,racket:exn:fail:syntax?"
prim__isExnFailSyntax : AnyPtr -> Bool

export
isExnFailSyntax : t -> Bool
isExnFailSyntax = prim__isExnFailSyntax . believe_me

export
data ExnFailSyntax : Type where [external]

export
IsExn ExnFailSyntax where

export
IsExnFail ExnFailSyntax where

export
IsExnFailSyntax ExnFailSyntax where

-- exn:fail:syntax:unbound

public export
interface IsExnFailSyntax e => IsExnFailSyntaxUnbound (e : Type) where

%foreign "scheme,racket:exn:fail:syntax:unbound?"
prim__isExnFailSyntaxUnbound : AnyPtr -> Bool

export
isExnFailSyntaxUnbound : t -> Bool
isExnFailSyntaxUnbound = prim__isExnFailSyntaxUnbound . believe_me

export
data ExnFailSyntaxUnbound : Type where [external]

export
IsExn ExnFailSyntaxUnbound where

export
IsExnFail ExnFailSyntaxUnbound where

export
IsExnFailSyntax ExnFailSyntaxUnbound where

export
IsExnFailSyntaxUnbound ExnFailSyntaxUnbound where

-- exn:fail:syntax:missing-module

public export
interface IsExnFailSyntax e => IsExnFailSyntaxMissingModule (e : Type) where

%foreign "scheme,racket:exn:fail:syntax:missing-module?"
prim__isExnFailSyntaxMissingModule : AnyPtr -> Bool

export
isExnFailSyntaxMissingModule : t -> Bool
isExnFailSyntaxMissingModule = prim__isExnFailSyntaxMissingModule . believe_me

export
data ExnFailSyntaxMissingModule : Type where [external]

export
IsExn ExnFailSyntaxMissingModule where

export
IsExnFail ExnFailSyntaxMissingModule where

export
IsExnFailSyntax ExnFailSyntaxMissingModule where

export
IsExnFailSyntaxMissingModule ExnFailSyntaxMissingModule where

-- exn:fail:read

public export
interface IsExnFail e => IsExnFailRead (e : Type) where

%foreign "scheme,racket:exn:fail:read?"
prim__isExnFailRead : AnyPtr -> Bool

export
isExnFailRead : t -> Bool
isExnFailRead = prim__isExnFailRead . believe_me

export
data ExnFailRead : Type where [external]

export
IsExn ExnFailRead where

export
IsExnFail ExnFailRead where

export
IsExnFailRead ExnFailRead where

-- exn:fail:read:eof

public export
interface IsExnFailRead e => IsExnFailReadEof (e : Type) where

%foreign "scheme,racket:exn:fail:read:eof?"
prim__isExnFailReadEof : AnyPtr -> Bool

export
isExnFailReadEof : t -> Bool
isExnFailReadEof = prim__isExnFailReadEof . believe_me

export
data ExnFailReadEof : Type where [external]

export
IsExn ExnFailReadEof where

export
IsExnFail ExnFailReadEof where

export
IsExnFailRead ExnFailReadEof where

export
IsExnFailReadEof ExnFailReadEof where

-- exn:fail:read:non-char

public export
interface IsExnFailRead e => IsExnFailReadNonChar (e : Type) where

%foreign "scheme,racket:exn:fail:read:non-char?"
prim__isExnFailReadNonChar : AnyPtr -> Bool

export
isExnFailReadNonChar : t -> Bool
isExnFailReadNonChar = prim__isExnFailReadNonChar . believe_me

export
data ExnFailReadNonChar : Type where [external]

export
IsExn ExnFailReadNonChar where

export
IsExnFail ExnFailReadNonChar where

export
IsExnFailRead ExnFailReadNonChar where

export
IsExnFailReadNonChar ExnFailReadNonChar where

-- exn:fail:network

public export
interface IsExnFail e => IsExnFailNetwork (e : Type) where

%foreign "scheme,racket:exn:fail:network?"
prim__isExnFailNetwork : AnyPtr -> Bool

export
isExnFailNetwork : t -> Bool
isExnFailNetwork = prim__isExnFailNetwork . believe_me

export
data ExnFailNetwork : Type where [external]

export
IsExn ExnFailNetwork where

export
IsExnFail ExnFailNetwork where

export
IsExnFailNetwork ExnFailNetwork where

-- exn:fail:network:errno

public export
interface IsExnFailNetwork e => IsExnFailNetworkErrno (e : Type) where

%foreign "scheme,racket:exn:fail:network:errno?"
prim__isExnFailNetworkErrno : AnyPtr -> Bool

export
isExnFailNetworkErrno : t -> Bool
isExnFailNetworkErrno = prim__isExnFailNetworkErrno . believe_me

export
data ExnFailNetworkErrno : Type where [external]

export
IsExn ExnFailNetworkErrno where

export
IsExnFail ExnFailNetworkErrno where

export
IsExnFailNetwork ExnFailNetworkErrno where

export
IsExnFailNetworkErrno ExnFailNetworkErrno where

-- exn:fail:out-of-memory

public export
interface IsExnFail e => IsExnFailOutOfMemory (e : Type) where

%foreign "scheme,racket:exn:fail:out-of-memory?"
prim__isExnFailOutOfMemory : AnyPtr -> Bool

export
isExnFailOutOfMemory : t -> Bool
isExnFailOutOfMemory = prim__isExnFailOutOfMemory . believe_me

export
data ExnFailOutOfMemory : Type where [external]

export
IsExn ExnFailOutOfMemory where

export
IsExnFail ExnFailOutOfMemory where

export
IsExnFailOutOfMemory ExnFailOutOfMemory where

-- exn:fail:unsupported

public export
interface IsExnFail e => IsExnFailUnsupported (e : Type) where

%foreign "scheme,racket:exn:fail:unsupported?"
prim__isExnFailUnsupported : AnyPtr -> Bool

export
isExnFailUnsupported : t -> Bool
isExnFailUnsupported = prim__isExnFailUnsupported . believe_me

export
data ExnFailUnsupported : Type where [external]

export
IsExn ExnFailUnsupported where

export
IsExnFail ExnFailUnsupported where

export
IsExnFailUnsupported ExnFailUnsupported where

-- exn:fail:user

public export
interface IsExnFail e => IsExnFailUser (e : Type) where

%foreign "scheme,racket:exn:fail:user?"
prim__isExnFailUser : AnyPtr -> Bool

export
isExnFailUser : t -> Bool
isExnFailUser = prim__isExnFailUser . believe_me

export
data ExnFailUser : Type where [external]

export
IsExn ExnFailUser where

export
IsExnFail ExnFailUser where

export
IsExnFailUser ExnFailUser where

-- exn:break

public export
interface IsExn e => IsExnBreak (e : Type) where

%foreign "scheme,racket:exn:break?"
prim__isExnBreak : AnyPtr -> Bool

export
isExnBreak : t -> Bool
isExnBreak = prim__isExnBreak . believe_me

export
data ExnBreak : Type where [external]

export
IsExn ExnBreak where

export
IsExnBreak ExnBreak where

-- exn:break:hangup

public export
interface IsExn e => IsExnBreakHangup (e : Type) where

%foreign "scheme,racket:exn:break:hangup?"
prim__isExnBreakHangup : AnyPtr -> Bool

export
isExnBreakHangup : t -> Bool
isExnBreakHangup = prim__isExnBreakHangup . believe_me

export
data ExnBreakHangup : Type where [external]

export
IsExn ExnBreakHangup where

export
IsExnBreak ExnBreakHangup where

export
IsExnBreakHangup ExnBreakHangup where

-- exn:break:terminate

public export
interface IsExn e => IsExnBreakTerminate (e : Type) where

%foreign "scheme,racket:exn:break:terminate?"
prim__isExnBreakTerminate : AnyPtr -> Bool

export
isExnBreakTerminate : t -> Bool
isExnBreakTerminate = prim__isExnBreakTerminate . believe_me

export
data ExnBreakTerminate : Type where [external]

export
IsExn ExnBreakTerminate where

export
IsExnBreak ExnBreakTerminate where

export
IsExnBreakTerminate ExnBreakTerminate where
