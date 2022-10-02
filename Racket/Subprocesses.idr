module Racket.Subprocesses

import Data.Either
import Ffiglet
import Racket.Basics
import Racket.Events
import Racket.Lists
import Racket.Pairs
import Racket.Ports
import Racket.Util

export
data Subprocess : Type where [external]

export
IsEvent Subprocess Subprocess where -- synchronises to itself like so many things in racket

%foreign "scheme,racket:subprocess-status"
prim__subprocessStatus : Subprocess -> PrimIO AnyPtr

export
subprocessStatus : HasIO io => Subprocess -> io (Maybe Int)
subprocessStatus s = do
  safeCast <$> (primIO $ prim__subprocessStatus s)

%foreign "scheme,racket:subprocess-wait"
prim__subprocessWait : Subprocess -> PrimIO ()

export
subprocessWait : HasIO io => Subprocess -> io ()
subprocessWait p = primIO $ prim__subprocessWait p

%foreign "scheme,racket:subprocess-pid"
prim__subprocessPid : Subprocess -> PrimIO (Falsifiable Int)

export
subprocessPid : HasIO io => Subprocess -> io (Maybe Int)
subprocessPid p = unfalsifiable <$> primIO (prim__subprocessPid p)

%foreign "scheme,racket:subprocess-kill"
prim__subprocessKill : Subprocess -> Bool -> PrimIO ()

export
subprocessKill : HasIO io => Subprocess -> Bool -> io ()
subprocessKill s b = primIO $ prim__subprocessKill s b

public export
data Pipe = OpenPipe

public export
data StderrPipe = OpenStderrPipe | CombineWithStdout

public export
data Group = NewGroup | NoGroup | GroupFrom Subprocess

public export
record Ports where
  constructor MkPorts
  stdin  : Maybe OutputFileStreamPort
  stdout : Maybe InputFileStreamPort
  stderr : Maybe InputFileStreamPort

%foreign """
scheme,racket:(lambda (stdin stdout stderr group command args)
  (call-with-values (apply subprocess-start stdin stdout stderr group command args) list))
"""
prim__subprocessStart : a -> b -> c -> d -> String -> Conses String -> PrimIO e

stderrArg : Either StderrPipe InputFileStreamPort -> AnyPtr
stderrArg (Left OpenStderrPipe) = believe_me False
stderrArg (Left CombineWithStdout) = believe_me (symbol "stdout")
stderrArg (Right port) = believe_me port

ungroup : Group -> AnyPtr
ungroup NewGroup = believe_me $ symbol "new"
ungroup NoGroup = believe_me False
ungroup (GroupFrom p) = believe_me p

||| Starts a subprocess. File stream ports may be given for input/output or new ports may be opened
||| for you (in which case they must be closed after the process exits.)
|||
||| Note that thanks to the wonders of unix, this always succeeds and you'll need to actually
||| monitor the subprocess somehow to determine if it actually failed.
export
subprocessStart
  :  HasIO io
  => (stdin  : Either Pipe OutputFileStreamPort)
  -> (stdout : Either Pipe InputFileStreamPort)
  -> (stderr : Either StderrPipe InputFileStreamPort)
  -> Group
  -> (command : String)
  -> (args : List String)
  -> io (Subprocess, Ports)
subprocessStart stdin stdout stderr group command args =
  translate <$> primIO (prim__subprocessStart
    (falsifiable $ eitherToMaybe stdout)
    (falsifiable $ eitherToMaybe stdin)
    (stderrArg stderr)
    (ungroup group) command (fromList args))
  where
    Raw : Type
    Raw = HConses
      [ Subprocess
      , Falsifiable InputFileStreamPort
      , Falsifiable OutputFileStreamPort
      , Falsifiable InputFileStreamPort ]
    translate : Raw -> (Subprocess, Ports)
    translate raw = 
      let proc   = car raw
          stdout = unfalsifiable (cadr raw)
          stdin  = unfalsifiable (caddr raw)
          stderr = unfalsifiable (cadddr raw)
      in (proc, MkPorts stdin stdout stderr)

-- giving up on the dependent version for now...

-- RawSubprocessPorts
--   :  (stdin  : Either Pipe OutputFileStreamPort)
--   -> (stdout : Either Pipe InputFileStreamPort)
--   -> (stderr : Either StderrPipe InputFileStreamPort)
--   -> Type
-- RawSubprocessPorts (Left _)  (Left _)  (Left _)  = HConses [Subprocess, OutputFileStreamPort, InputFileStreamPort, InputFileStreamPort]
-- RawSubprocessPorts (Left _)  (Left _)  (Right _) = HConses [Subprocess, OutputFileStreamPort, InputFileStreamPort]
-- RawSubprocessPorts (Left _)  (Right _) (Left _)  = HConses [Subprocess, OutputFileStreamPort, (), InputFileStreamPort]
-- RawSubprocessPorts (Left _)  (Right _) (Right _) = HConses [Subprocess, OutputFileStreamPort]
-- RawSubprocessPorts (Right _) (Left _)  (Left _)  = HConses [Subprocess, (), InputFileStreamPort, InputFileStreamPort]
-- RawSubprocessPorts (Right _) (Left _)  (Right _) = HConses [Subprocess, (), InputFileStreamPort]
-- RawSubprocessPorts (Right _) (Right _) (Left _)  = HConses [Subprocess, (), (), InputFileStreamPort]
-- RawSubprocessPorts (Right _) (Right _) (Right _) = HConses [Subprocess]

-- SubprocessPorts
--   :  (stdin  : Either Pipe OutputFileStreamPort)
--   -> (stdout : Either Pipe InputFileStreamPort)
--   -> (stderr : Either StderrPipe InputFileStreamPort)
--   -> Type
-- SubprocessPorts (Left _)  (Left _)  (Left _)  = (OutputFileStreamPort, InputFileStreamPort, InputFileStreamPort)
-- SubprocessPorts (Left _)  (Left _)  (Right _) = (OutputFileStreamPort, InputFileStreamPort)
-- SubprocessPorts (Left _)  (Right _) (Left _)  = (OutputFileStreamPort, InputFileStreamPort)
-- SubprocessPorts (Left _)  (Right _) (Right _) = OutputFileStreamPort
-- SubprocessPorts (Right _) (Left _)  (Left _)  = (InputFileStreamPort, InputFileStreamPort)
-- SubprocessPorts (Right _) (Left _)  (Right _) = InputFileStreamPort
-- SubprocessPorts (Right _) (Right _) (Left _)  = InputFileStreamPort
-- SubprocessPorts (Right _) (Right _) (Right _) = ()

-- export
-- depSubprocessStart
--   :  HasIO io
--   => (stdin  : Either Pipe OutputFileStreamPort)
--   -> (stdout : Either Pipe InputFileStreamPort)
--   -> (stderr : Either StderrPipe InputFileStreamPort)
--   -> Group
--   -> (command : String)
--   -> (args : List String)
--   -> io (Subprocess, SubprocessPorts stdin stdout stderr)
-- depSubprocessStart stdin stdout stderr group command args =
--   translate <$> primIO (prim__subprocessStart
--     (falsifiable $ eitherToMaybe stdout)
--     (falsifiable $ eitherToMaybe stdin)
--     (stderrArg stderr)
--     (ungroup group) command (fromList args))
--   where
--     translate : RawSubprocessPorts i o e -> (Subprocess, SubprocessPorts i o e)
--     translate ports =
--       case (stdin, stdout, stderr) of
--         (Left _,  Left _,  Left _)  => ?ha -- (OutputFileStreamPort, InputFileStreamPort, InputFileStreamPort)
--         (Left _,  Left _,  Right _) => ?hb -- (OutputFileStreamPort, InputFileStreamPort)
--         (Left _,  Right _, Left _)  => ?hc -- (OutputFileStreamPort, InputFileStreamPort)
--         (Left _,  Right _, Right _) => ?hd -- OutputFileStreamPort
--         (Right _, Left _,  Left _)  => ?he -- (InputFileStreamPort, InputFileStreamPort)
--         (Right _, Left _,  Right _) => ?hf -- InputFileStreamPort
--         (Right _, Right _, Left _)  => ?hg -- InputFileStreamPort
--         (Right _, Right _, Right _) => (car ports, ?hh)
--     -- translate ra/w = 
--     --   let proc = car raw
--     --       stdout = unfalsifiable $ car (cdr raw)
--     --       stdin = unfalsifiable $ car (cdr (cdr raw))
--     --       stderr = unfalsifiable $ car (cdr (cdr (cdr raw)))
--     --   in (proc, MkPorts stdin stdout stderr)
