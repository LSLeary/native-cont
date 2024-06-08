
-- --< Header >-- {{{

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

{-|

Description : Loops with 'break' and 'continue', implemented via /native-cont/.
Copyright   : (c) L. S. Leary, 2024

Loops with 'break' and 'continue'.

-}

-- }}}

-- --< Imports & Exports >-- {{{

module Control.Continuation.Loop (

  Scope,

  -- * Loop #Loop#
  Loop, loop,

  -- ** Derived Loops #Loop:Derived_Loops#
  -- $Derived_Loops
  for, while,

  -- ** Control #Loop:Control#
  continue, break,

) where

-- base
import Prelude hiding (return, break)

import Data.Type.Equality (TestEquality(..))
import Data.Functor ((<&>))
import Control.Monad (forever)

-- native-cont
import Control.Continuation
  (Scope, Cont, Limit, sameLimit, impose, type (<|), newSTRef)
import Control.Continuation.Inferred
  (δ, delimit, lower, return, readSTRef, writeSTRef)

-- }}}

-- --< Loop >-- {{{

-- | Scope @p@ is the body of a loop: within, one may 'continue' immediately to the next iteration or 'break' out entirely.
data Loop p where
  Loop
    :: p <| q
    => { inner :: {-# UNPACK #-} !(Limit p q ())
       , outer :: {-# UNPACK #-} !(Limit q r ())
       }
    -> Loop p

instance TestEquality Loop where
  Loop{ inner = i1 } `testEquality` Loop{ inner = i2 }
    = i1 `sameLimit` i2 <&> \(eq, _, _) -> eq

{- | Enter a loop.

==== Reduction Semantics

\( \declare[hs]{loop} \hsloop \app \lambda \) is treated as a /loop binder/ under which execution continues.
Contrary to /native-cont/ conventions, we reuse \( l \) as a loop metavariable.
In particular, \( l_b \) indicates a loop associated with body \( e_b \). \[
  {\E} \sq{\hsloop \app \lam {l_b} \pure \app \unit}
    \step^*
  {\E} \sq{\hsloop \app \lam {l_b} {e_b}}
\]

-}
loop :: (forall p. p <| q => Loop p -> Cont p ()) -> Cont q ()
loop f = delimit \outer -> δ\inner -> forever do
  impose inner (f Loop{inner,outer})

-- }}}

-- --< Loop / Derived Loops >-- {{{

-- $Derived_Loops
-- These loops derive from 'loop' and 'break'; see source for detail.

-- | Loop while a condition holds.
while
  :: Cont q Bool
  -> (forall p. p <| q => Loop p -> Cont p ())
  -> Cont q ()
while cond f = loop \l -> lower cond >>= \case
  False -> break l
  True  -> f l

-- | Loop once for each element of a list.
for :: [a] -> (forall p. p <| q => Loop p -> a -> Cont p ()) -> Cont q ()
for xs f = do
  r <- newSTRef xs
  loop \l -> readSTRef r >>= \case
    [  ] -> break l
    y:ys -> do
      writeSTRef r ys
      f l y

-- }}}

-- --< Loop / Control >-- {{{

{- | Continue to the next iteration of @t'Loop' q@ immediately.

==== Reduction Semantics

\[
\declare{continue}
  {\E}_1 \sq{ \hsloop \app \lam {l_b} {{\E}_2 \sq{\continue \app l_b}} }
    \step^*
  {\E}_1 \sq{\hsloop \app \lam {l_b} {\pure \app \unit}}
\]

-}
continue :: p <| q => Loop q -> Cont p a
continue Loop{inner} = return inner ()

{- | Break out of @t'Loop' q@.

==== Reduction Semantics

\[
\declare[hs]{break}
  {\E}_1 \sq{ \hsloop \app \lam l {{\E}_2 \sq{\hsbreak \app l}} }
    \step^*
  {\E}_1 \sq{\pure \app \unit}
\]

-}
break :: p <| q => Loop q -> Cont p a
break Loop{outer} = return outer ()

-- }}}

