module Racket.Hashes

import Racket.Util

-- Technically, hashes are also parameterised by their equivalence relation, but ugh, i'm not sure
-- we even care, who wants to use racket hashes when you can have idris maps?
export
data Hash : (k : Type) -> (v : Type) -> Type where [external]

%foreign "scheme,racket:hash?"
prim__isHash : AnyPtr -> Bool

export %inline
isHash : a -> Bool
isHash = prim__isHash . believe_me

%foreign "scheme,racket:hash-ref"
prim__hashRef : AnyPtr -> AnyPtr -> AnyPtr -> AnyPtr

export
-- there are times when i find racket's ways of doing things absolutely batshit insane. this is one
-- of them.
hashRef : k -> Hash k v -> Maybe v
hashRef k h = unfalsifiable $ believe_me $ prim__hashRef (believe_me h) (believe_me k) (believe_me False)
