# *native-cont*

A safe interface to the delimited continuation primops.

## Design

A delimited control operator is defined only beneath a corresponding delimiter.
The core idea of *native-cont* is to hence achieve safety by representing the *scope* of a computation at the type level.
```haskell
type Cont :: Scope -> Type -> Type
```
A delimiter then delimits a subscope from its immediate superscope
```haskell
type Limit :: Scope -> Scope -> Type -> Type
```
and every new `Limit` creates a corresponding subscope.
```haskell
newLimit :: (forall q. q <| r => Limit q r a -> Cont r b) -> Cont r b
```
To actually enter that subscope, the `Limit` must be `impose`d.
```haskell
impose :: Limit q r a -> Cont q a -> Cont r a
```
Within, it's safe to `sunder` the continuation at the `Limit`.
```haskell
sunder
  :: p <| q
  => Limit q r a
  -> ((Cont p b -> Cont q a) -> Cont r a)
  -> Cont p b
```
This type signature shows the payoff of our scoping discipline.
Read in English:
  * In any subscope `p` of `q`, we may `sunder` the continuation at the juncture of scopes `q` and `r`.
  * Doing so captures the continuation up to scope `q` and throws us into scope `r`.

You can run `Cont` in the `RealWorld`, but it requires `IO`:
```haskell
runContIO :: Cont RealWorld a -> IO a
```
This in turn allows `IO` within:
```haskell
runIO :: p <| RealWorld => IO a -> Cont p a
```
To run `Cont` in a pure context we must instead isolate it to its own universe:
```haskell
runCont :: (forall u. Cont u a) -> a
```

## Get a Look at These Beauties

There are a lot of similar delimited control operators that do subtly different things with the delimiter.
Too subtle, in fact, to be distinguished by type in prior art (to my knowledge).
In *native-cont* however, it is not so—behold!

```haskell
control0 :: p <| q => Limit q r a -> ((Cont p b -> Cont q a) -> Cont r a) -> Cont p b
shift0   :: p <| q => Limit q r a -> ((Cont p b -> Cont r a) -> Cont r a) -> Cont p b
control  :: p <| q => Limit q r a -> ((Cont p b -> Cont q a) -> Cont q a) -> Cont p b
shift    :: p <| q => Limit q r a -> ((Cont p b -> Cont r a) -> Cont q a) -> Cont p b
```

The differences in their behaviour can be read from the type signatures!
Further, they can no longer be confused—if you accidentally use the wrong one, the type checker will set you straight.

## Cheatsheet

   | `GHC.Exts`       | `NativeCont`   | `Control.Continuation.*` |
   |------------------|----------------|--------------------------|
   | `PromptTag# a`   | `Limit# _ _ a` | `Limit _ _ a`            |
   | `newPromptTag#`  | `newLimit#`    | `newLimit`               |
   | `samePromptTag#` | `sameLimit#`   | `sameLimit`              |
   | `prompt#`        | `impose#`      | `impose`                 |
   | `control0#`      | `sunder#`      | `sunder`                 |

## Sublibraries

Beyond the core library, this package provides several public sublibraries:

  * *native-cont:loop*
      * Loops with `break` and `continue`.
  * *native-cont:exception*
      * Checked exceptions.
  * *native-cont:handler*
      * `yield`ing values to handlers `install`ed at `Limit`s.
  * *native-cont:coroutine*
      * Coroutines.
  * *native-cont:algebraic*
      * Algebraic effects.

The purpose of these libraries is, in order:

  1. To test the interface of the core library.
  2. To be usage examples for the core library.
  3. To provide additional functionality compatible with the core offerings.

