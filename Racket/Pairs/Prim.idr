module Racket.Pairs.Prim

export
%foreign "scheme,racket:pair?"
prim__isPair : AnyPtr -> Bool

export
%foreign "scheme,racket:null?"
prim__isNull : AnyPtr -> Bool

export
%foreign "scheme,racket:cons"
prim__cons : AnyPtr -> AnyPtr -> AnyPtr

export
%foreign "scheme,racket:car"
prim__car : AnyPtr -> AnyPtr

export
%foreign "scheme,racket:cdr"
prim__cdr : AnyPtr -> AnyPtr

export
%foreign "scheme,racket:(lambda () null)"
prim__null : AnyPtr

export
%foreign "scheme:map"
prim__map : AnyPtr -> AnyPtr -> AnyPtr

export
%foreign "scheme:append"
prim__append : AnyPtr -> AnyPtr -> AnyPtr

export
%foreign "scheme,racket:append"
prim__appendStar : AnyPtr -> AnyPtr

export
%foreign "scheme,racket:append-map"
prim__appendMap : AnyPtr -> AnyPtr -> AnyPtr

export
%foreign "scheme:length"
prim__length : AnyPtr -> AnyPtr

export
%foreign "scheme,racket:(lambda (f a b) (for/list ([a a] [b b]) (f a b)))"
prim__zipWith : (AnyPtr -> AnyPtr -> AnyPtr) -> AnyPtr -> AnyPtr -> AnyPtr

export
%foreign "scheme,racket:cartesian-product"
prim__cartesianProduct2 : AnyPtr -> AnyPtr -> AnyPtr

