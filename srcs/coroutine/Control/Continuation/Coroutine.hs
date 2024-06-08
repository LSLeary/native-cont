
-- --< Header >-- {{{

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

{-|

Description : Coroutines implemented via /native-cont:handler/.
Copyright   : (c) L. S. Leary, 2024

Coroutines implemented via /native-cont:handler/.

We decline to develop reduction semantics for coroutines, as doing so with our current machinery would be noisy and not particularly enlightening.
Extending that machinery with the reference handling necessary to do better is beyond the scope of /native-cont/.

-}

-- }}}

-- --< Imports & Exports >-- {{{

module Control.Continuation.Coroutine (

  -- * Coroutine #Coroutine#
  Coroutine,
  newCoroutine,

  -- ** Yield #Coroutine:Yield#
  Yield,
  yield,

  -- ** Resume #Coroutine:Resume#
  resume,
  Result(..),

) where

-- base
import Data.Functor (($>))
import Control.Monad.Fix (MonadFix(..))

-- native-cont
import Control.Continuation.Inferred

-- native-cont:handler
import qualified Control.Continuation.Handler.Inferred as H

-- }}}

-- --< Coroutine >-- {{{

-- There's a direct correspondence between the status of the coroutine and the result of resuming it, hence 'Result' is suitable for representing both.
-- We just need to reinterpret 'Yielded' as "yielded control", i.e. paused.
type Status p x y = Result (x -> Cont p y)

-- | A coroutine born of the scope @p@, running in a direct subscope thereof.
--   It may be 'resume'd with an @x@ to 'yield' a @y@.
newtype Coroutine p x y = Coroutine{ status :: STRef p (Status p x y) }
  deriving Eq

-- | Given the right to 'yield' @y@s and the initial @x@, create a new t'Coroutine' executing the supplied action.
--   The @Coroutine@ is born /paused/.
newCoroutine
  :: (forall p. p <| q => Yield p x y -> x -> Cont p y) {- ^ -}
  -> Cont q (Coroutine q x y)
newCoroutine co = Coroutine <$> mfix \status ->
  newSTRef $ Yielded \x -> delimit \l -> do
    let h = H.install l \y k -> writeSTRef status (Yielded $ k . pure) $> y
    co (Yield $ H.yield h) x <* writeSTRef status  Finished

-- }}}

-- --< Yield >-- {{{

-- | A @Yield p x y@ witnesses that its corresponding t'Coroutine' may 'yield' a @y@ from scope @p@ and receive an @x@ in turn.
newtype Yield p x y = Yield{ yield_ :: y -> Cont p x }

-- | Yield control and a @y@, waiting to be resumed with an @x@.
yield :: p <| q => Yield q x y -> y -> Cont p x
yield Yield{yield_} y = lower (yield_ y)

-- }}}

-- --< Resume >-- {{{

-- | Resume a paused t'Coroutine'. Fails if the @Coroutine@ is already 'Running' or has 'Finished'.
resume :: p <| q => Coroutine q x y -> x -> Cont p (Result y)
resume Coroutine{status} x = readSTRef status >>= traverse \resume_ -> do
  writeSTRef status Running
  lower (resume_ x)

-- | The possible results of resuming a t'Coroutine'.
data Result a = Running | Yielded a | Finished
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable)

-- }}}

