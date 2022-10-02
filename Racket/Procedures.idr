module Racket.Procedures

%foreign "scheme,racket:(lambda (f) (f))"
prim__call0 : AnyPtr -> PrimIO AnyPtr

export
unsafeCall0 : HasIO io => t -> io u
unsafeCall0 f = primIO $ believe_me $ prim__call0 (believe_me f)

%foreign "scheme,racket:(lambda (f a) (f a))"
prim__call1 : AnyPtr -> AnyPtr -> PrimIO AnyPtr

export
unsafeCall1 : HasIO io => t -> u -> io v
unsafeCall1 f a = primIO $ believe_me $ prim__call1 (believe_me f) (believe_me a)

%foreign "scheme,racket:(lambda (f a b) (f a b))"
prim__call2 : AnyPtr -> AnyPtr -> AnyPtr -> PrimIO AnyPtr

export
unsafeCall2 : HasIO io => t -> u -> v -> io w
unsafeCall2 f a b = primIO $ believe_me $ prim__call2 (believe_me f) (believe_me a) (believe_me b)
