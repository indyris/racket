# Racket - FFI bindings for idris2 on racket

# Implementation status

Fully implemented:

* Cons pairs
* Custodian Boxes

Mostly implemented:

* Custodians
* Environment Variables

Partially implemented:

* Cons extras (HList, HVec)
* Subprocesses
* Time

## `Control.Play`

`Control.Play` is a fork of Edwin's excellent `Control.App` but with a focus on enabling seamless
use over FFI boundaries.

We probably suck in a bunch of ways, not least related to linear resources, but let's see where this
goes...

Some of this documentation is also going to be relevant to `Control.App` if you're having difficulty
understanding that.

### Unlifting

I am writing a build tool and it needs to do a lot of FFI. In particular, because of the way the
racket standard library works, i have to use primitives that take callbacks. Unfortunately, we are
limited to passing ordinary functions across the FFI boundary. To put this another way, we have to
lower everything to `PrimIO` before passing it across the boundary. This is annoying enough as a
library author, but when I come to actually use the tool and write scripts that cross the FFI
boundary, that's just not going to work for me....

#### unliftio

There is already a haskell library implementing a solution, `unliftIO`. Haskell has no `PrimIO`, so
everything is lowered to `IO` thus:

```haskell
class MonadIO m => MonadUnliftIO m where
  withRunInIO :: ((forall a. m a -> IO a) -> IO b) -> m b
```

This type signature looks odd, so let's pick it apart:

* It's a function returning `m b` for for `MonadIO m`. This has to be true so the context of `m` is
  available to be lowered.
* It takes a function that returns an `IO b`, because the purpose is to run some `IO` code.
* That function takes a function from `m a -> IO a` - i.e. you are given a lowering function.

#### Lower

I chose to make mine more generic, allowing you to lower across arbitrary `Type -> Type` (we are
going to say "monad", but we don't actually require a `Monad` (or any other!) instance):

```idris
interface Lower (0 l, m : Type -> Type) where
  constructor MkLower
  withLower : {0 a, b : Type} -> (callback : (lower : (1 _ : m a) -> l a) -> l b) -> m b
```

* `m` is the source (higher) monad.
* `l` is the destination (lower) monad.
* It's called `Lower` because it's no longer fixed to `Monad` or `IO` and we think it's a better
  name than `Unlift`.
* `withRunInIO` is now called `withLower` to represent that the callback takes an arbitrary lowering
  function as parameter.
* `withLower`'s type is essentially a direct generalisation of the haskell, but with names and a
  curiously linear parameter to the `lower` function that we shall gloss over but to say it's
  required for `PrimIO`.

### The `Play` monad

```idris
data Play : (effects : List Effect) -> (t : Type) -> Type where
```

Aside from the effects list, it's an ordinary monad with a return type as the last parameter.

The effects list specifies which side effects are currently available for use. Whereas in haskell
you might use monad transformers to stack effects, with `Play`, we put effects in this list.

Effects are typically introduced with an effect-specific `run` function that takes as its last
parameter a `Play (e :: es) t` indicating that the effect is available in the subcomputation.

So how does this work? Essentially, effects are just type-safe exceptions you `throw` and those
`run` functions just `catch` them and and deal with them as appropriate. By making the constructors
of your type private and providing wrapper functions, you can limit how they are used.

#### Simple usage

```idris
import Play

-- These empty types are just names for our effects.
data FortyTwo   : Type where -- This is going to be a reader
data FourTwenty : Type where -- This is going to be a register (state)

main : IO ()
main = runPlay $                 -- run a play computation in IO
  runReader FortyTwo 42 $        -- add a reader effect called `FortyTwo` with the value `42`
  runReg FourTwenty 420 $ do     -- run a register effect called `FourTwenty` with the value `420`
    fortyTwo <- ask FortyTwo     -- read the reader `FortyTwo`, receiving 42
    fourTwenty <- get FourTwenty -- read the register `FourTwenty`, receiving 420
    put FourTwenty 420           -- write the value 420 back into register `FourTwenty`
    println $                    -- and show some output.
      "42: " <> show fortyTwo <> ", 420: " <> fourTwenty 
```

## Copyright and License

Copyright (c) 2022 James Laver

