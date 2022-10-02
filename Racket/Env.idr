module Racket.Env

import Ffiglet
import Racket.Basics
import Racket.Lists
import Racket.Parameters

export
data EnvVars : Type where [external]

export
ToFFI EnvVars EnvVars where toFFI = id

export
FromFFI EnvVars EnvVars where fromFFI = Just

%foreign "scheme,racket:environment-variables?"
prim__isEnvVars : AnyPtr -> Bool

export
isEnvVars : t -> Bool
isEnvVars = prim__isEnvVars . believe_me

export
SafeCast EnvVars where
  safeCast ptr = if isEnvVars ptr then Just (believe_me ptr) else Nothing

%foreign "scheme,racket:environment-variables-ref"
prim__lookup : AnyPtr -> AnyPtr -> PrimIO AnyPtr

export
lookupEnv : String -> EnvVars -> Maybe String
lookupEnv key e = safeCast $ prim__lookup (believe_me e) (believe_me key)

%foreign "scheme,racket:environment-variables-set!"
prim__set : AnyPtr -> AnyPtr -> AnyPtr -> PrimIO ()

export
setEnv : HasIO io => String -> String -> EnvVars -> io ()
setEnv k v e = primIO $ prim__set (believe_me e) (believe_me k) (believe_me v)

export
unsetEnv : HasIO io => String -> EnvVars -> io ()
unsetEnv k e = primIO $ prim__set (believe_me e) (believe_me k) (believe_me False)

%foreign "scheme,racket:environment-variables-names"
prim__keys : AnyPtr -> PrimIO (Conses String)

export
envVarKeys : HasIO io => EnvVars -> io (Conses String)
envVarKeys e = primIO $ prim__keys (believe_me e)

%foreign "scheme,racket:(lambda () current-environment-variables)"
prim__currentEnvVars : PrimIO (Parameter EnvVars)

export
currentEnvVars : HasIO io => io (Parameter EnvVars)
currentEnvVars = primIO prim__currentEnvVars

export
getCurrentEnvVars : HasIO io => io EnvVars
getCurrentEnvVars = currentEnvVars >>= readParameter

export
setCurrentEnvVars : HasIO io => EnvVars -> io ()
setCurrentEnvVars e = currentEnvVars >>= \f => writeParameter f e

%foreign "scheme,racket:environment-variables-copy"
prim__copy : AnyPtr -> AnyPtr

export
forkEnv : EnvVars -> EnvVars
forkEnv = believe_me . prim__copy . believe_me

%foreign "scheme,racket:string-environment-variable-name"
prim__isStringEnvVarName : AnyPtr -> Bool

export
isStringEnvVarName : t -> Bool
isStringEnvVarName = prim__isStringEnvVarName . believe_me


%foreign "scheme,racket:(lambda () (make-environment \"dummy\" \"\"))"
prim__dummyEnv : PrimIO EnvVars

export
cleanEnv : HasIO io => io EnvVars
cleanEnv = do
  e <- primIO $ prim__dummyEnv
  unsetEnv "dummy" $ the EnvVars e
  pure e
