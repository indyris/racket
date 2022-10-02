module Racket.Basics

import Ffiglet

-- Bools

%foreign "scheme,racket:boolean?"
prim__isBool : AnyPtr -> Bool

export
isBool : t -> Bool
isBool = prim__isBool . believe_me

Kind Bool where check = prim__isBool

export
SafeCast Bool where
  safeCast ptr = if isBool ptr then Just (believe_me ptr) else Nothing

%foreign "scheme,racket:false?"
prim__isFalse : AnyPtr -> Bool

export
isFalse : t -> Bool
isFalse = prim__isFalse . believe_me

%foreign "scheme,racket:integer?"
prim__isInt : AnyPtr -> Bool

export
isInt : t -> Bool
isInt = prim__isInt . believe_me

export
SafeCast Int where
  safeCast ptr = if isInt ptr then Just (believe_me ptr) else Nothing

-- Strings

%foreign "scheme,racket:string?"
prim__isString : AnyPtr -> Bool

export
isString : t -> Bool
isString = prim__isString . believe_me

Kind String where check = prim__isString

export
SafeCast String where
  safeCast ptr = if isString ptr then Just (believe_me ptr) else Nothing

-- Symbols

export
data Symbol : Type where [external]

%foreign "scheme,racket:symbol?"
prim__isSymbol : AnyPtr -> Bool

export
isSymbol : t -> Bool
isSymbol = prim__isSymbol . believe_me

Kind Symbol where check = prim__isSymbol

export
SafeCast Symbol where
  safeCast ptr = if isSymbol ptr then Just (believe_me ptr) else Nothing

%foreign "scheme,racket:string->symbol"
prim__symbol : String -> Symbol

export
symbol : String -> Symbol
symbol = prim__symbol

%foreign "scheme,racket:symbol->string"
prim__symbolToString : Symbol -> String

export
symbolToString : Symbol -> String
symbolToString = prim__symbolToString
