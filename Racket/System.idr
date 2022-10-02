module Racket.System

import Racket.Basics
import Racket.Pairs

%foreign "scheme,racket:system-type"
prim__systemType : Symbol -> AnyPtr

export
systemOSFamily : String
systemOSFamily = (symbolToString . believe_me) $ prim__systemType (symbol "os")

export
systemOS : String
systemOS = (symbolToString . believe_me) $ prim__systemType (symbol "os*")

export
systemArch : String
systemArch = (symbolToString . believe_me) $ prim__systemType (symbol "arch")

export
systemWordSize : Int
systemWordSize = believe_me $ prim__systemType (symbol "word")

export
systemVM : String
systemVM = (symbolToString . believe_me) $ prim__systemType (symbol "vm")

export
systemGC : String
systemGC = (symbolToString . believe_me) $ prim__systemType (symbol "gc")

export
systemLinkMode : String
systemLinkMode = (symbolToString . believe_me) $ prim__systemType (symbol "link")

export
systemMachine : String
systemMachine = believe_me $ prim__systemType (symbol "machine")

export
systemTargetMachine : String
systemTargetMachine = believe_me $ prim__systemType (symbol "target-machine")

export
systemSOSuffix : String
systemSOSuffix = believe_me $ prim__systemType (symbol "so-suffix")

export
systemSOMode : String
systemSOMode = believe_me $ prim__systemType (symbol "so-mode")

export
systemCross : String
systemCross = believe_me $ prim__systemType (symbol "cross")

public export
record FSChangeSupport where
  constructor MkFSChangeSupport
  supported  : Bool
  scalable   : Bool
  lowLatency : Bool
  fileLevel  : Bool

export
systemFSChangeSupport : FSChangeSupport
systemFSChangeSupport =
  let s2 = cdr support in
  let s3 = cdr s2 in
  let supported = car support in
  let scalable = car s2 in
  let lowLatency = car s3 in
  let fileLevel = car $ cdr s3 in
  MkFSChangeSupport supported scalable lowLatency fileLevel
  where
    support : Cons Bool $ Cons Bool $ Cons Bool $ Cons Bool Null
    support = believe_me $ prim__systemType (symbol "fs-change")

-- prim__systemlanguageCountry : AnyPtr -- typed `string?`
