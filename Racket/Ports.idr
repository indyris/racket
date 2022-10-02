module Racket.Ports

import Ffiglet

-- Input ports

export
%foreign "scheme,racket:input-port?"
isInputPort : a -> Bool

public export
interface IsInputPort (p : Type) where

export
data InputPort : Type where [external]

export
ToFFI InputPort InputPort where toFFI = id

export
FromFFI InputPort InputPort where fromFFI = Just

export
SafeCast InputPort where
  safeCast ptr = if isInputPort ptr then Just (believe_me ptr) else Nothing

export
IsInputPort InputPort where

%foreign "scheme,racket:close-input-port"
prim__closeInputPort : a -> PrimIO ()

export
closeInputPort : HasIO io => (0 _ : IsInputPort p) => p -> io ()
closeInputPort p = primIO $ prim__closeInputPort p

-- Output ports

export
%foreign "scheme,racket:output-port?"
isOutputPort : a -> Bool

public export
interface IsOutputPort (p : Type) where

export
data OutputPort : Type where [external]

export
ToFFI OutputPort OutputPort where toFFI = id

export
FromFFI OutputPort OutputPort where fromFFI = Just

export
SafeCast OutputPort where
  safeCast ptr = if isOutputPort ptr then Just (believe_me ptr) else Nothing

export
IsOutputPort OutputPort where

%foreign "scheme,racket:close-output-port"
prim__closeOutputPort : a -> PrimIO ()

export
closeOutputPort : HasIO io => (0 _ : IsOutputPort p) => p -> io ()
closeOutputPort p = primIO $ prim__closeOutputPort p

-- File stream ports

export
%foreign "scheme,racket:file-stream-port?"
isFileStreamPort : a -> Bool

public export
interface IsFileStreamPort (p : Type) where

export
data FileStreamPort : Type where [external]

export
ToFFI FileStreamPort FileStreamPort where toFFI = id

export
FromFFI FileStreamPort FileStreamPort where fromFFI = Just

export
SafeCast FileStreamPort where
  safeCast ptr =
    if isFileStreamPort ptr then Just (believe_me ptr) else Nothing

-- Input file stream ports

export
data InputFileStreamPort : Type where [external]

export
ToFFI InputFileStreamPort InputFileStreamPort where toFFI = id

export
FromFFI InputFileStreamPort InputFileStreamPort where fromFFI = Just

export
SafeCast InputFileStreamPort where
  safeCast ptr =
    if isInputPort ptr && isFileStreamPort ptr then Just (believe_me ptr) else Nothing

export
IsInputPort InputFileStreamPort where

export
IsFileStreamPort InputFileStreamPort where


--  Output file stream ports

export
data OutputFileStreamPort : Type where [external]

export
ToFFI OutputFileStreamPort OutputFileStreamPort where toFFI = id

export
FromFFI OutputFileStreamPort OutputFileStreamPort where fromFFI = Just

export
SafeCast OutputFileStreamPort where
  safeCast ptr =
    if isOutputPort ptr && isFileStreamPort ptr then Just (believe_me ptr) else Nothing

export
IsOutputPort OutputFileStreamPort where

export
IsFileStreamPort OutputFileStreamPort where

%foreign "scheme,racket:write"
prim__write : a -> p -> PrimIO ()

export
write : HasIO io => IsOutputPort p => a -> p -> io ()
write thing port = primIO (prim__write thing port)

%foreign "scheme,racket:make-input-port"
prim__makeInputPort : name -> readIn -> peek -> close -> getProgressEvt-> commit -> getLocation -> countLines -> initPosition -> bufferMode -> PrimIO a

%foreign "scheme,racket:make-output-port"
prim__makeOutputPort : name -> evt -> writeOut -> close -> writeOutSpecial -> getWriteEvt-> getWriteSpecialEvt -> getLocation -> countLines -> initPosition -> bufferMode -> PrimIO a

