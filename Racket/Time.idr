module Racket.Time

%foreign "scheme,racket:current-seconds"
prim__currentSeconds : PrimIO Int

export
currentSeconds : HasIO io => io Int
currentSeconds = primIO prim__currentSeconds

%foreign "scheme,racket:current-inexact-milliseconds"
prim__currentInexactMilliseconds : PrimIO Double

export
currentInexactMilliseconds : HasIO io => io Double
currentInexactMilliseconds = primIO prim__currentInexactMilliseconds

%foreign "scheme,racket:current-inexact-monotonic-milliseconds"
prim__currentInexactMonotonicMilliseconds : PrimIO Double

export
currentInexactMonotonicMilliseconds : HasIO io => io Double
currentInexactMonotonicMilliseconds = primIO prim__currentInexactMonotonicMilliseconds
 
