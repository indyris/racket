module Racket.Threads

import Racket.Custodians

export
data Thread : Type where [external]

%foreign "scheme,racket:thread"
prim__thread : PrimIO () -> PrimIO Thread

export
thread : HasIO io => IO () -> io Thread
thread act = primIO $ prim__thread $ toPrim act

%foreign "scheme,racket:thread?"
prim__isThread : AnyPtr -> Bool

export
isThread : a -> Bool
isThread = prim__isThread . believe_me

%foreign "scheme,racket:current-thread"
prim__currentThread : PrimIO Thread

export
currentThread : HasIO io => io Thread
currentThread = primIO prim__currentThread

%foreign "scheme,racket:thread/suspend-to-kill"
prim__threadSuspendToKill : PrimIO () -> PrimIO Thread

export
threadSuspendToKill : HasIO io => IO () -> io Thread
threadSuspendToKill act = primIO $ prim__threadSuspendToKill $ toPrim act

%foreign "scheme,racket:call-in-nested-thread"
prim__callInNestedThread1 : PrimIO a -> PrimIO a

export
callInNestedThread : HasIO io => IO a -> io a
callInNestedThread act = primIO $ prim__callInNestedThread1 (toPrim act)

%foreign "scheme,racket:call-in-nested-thread"
prim__callInNestedThread2 : PrimIO a -> Custodian -> PrimIO a

export
callInNestedThread' : HasIO io => IO a -> Custodian -> io a
callInNestedThread' act cust = primIO $ prim__callInNestedThread2 (toPrim act) cust

%foreign "scheme,racket:thread-suspend"
prim__threadSuspend : Thread -> PrimIO ()

export
threadSuspend : HasIO io => Thread -> io ()
threadSuspend act = primIO $ prim__threadSuspend $ act

%foreign "scheme,racket:thread-resume"
prim__threadResume1 : Thread -> PrimIO ()

export
threadResume : HasIO io => Thread -> io ()
threadResume act = primIO $ prim__threadResume1 $ act

%foreign "scheme,racket:thread-resume"
prim__threadResume2 : Thread -> Custodian -> PrimIO ()

export
threadResume' : HasIO io => Thread -> Custodian -> io ()
threadResume' thread custodian = primIO $ prim__threadResume2 thread custodian

%foreign "scheme,racket:kill-thread"
prim__threadKill : Thread -> PrimIO ()

export
threadKill : HasIO io => Thread -> io ()
threadKill act = primIO $ prim__threadKill $ act

%foreign "scheme,racket:thread-suspend"
prim__sleep : Double -> PrimIO ()

export
sleep : HasIO io => Double -> io ()
sleep secs = primIO $ prim__sleep secs

%foreign "scheme,racket:thread-running?"
prim__isThreadRunning : Thread -> PrimIO Bool

export
isThreadRunning : HasIO io => Thread -> io Bool
isThreadRunning thread = primIO $ prim__isThreadRunning thread

%foreign "scheme,racket:thread-dead?"
prim__isThreadDead : Thread -> PrimIO Bool

export
isThreadDead : HasIO io => Thread -> io Bool
isThreadDead thread = primIO $ prim__isThreadDead thread
