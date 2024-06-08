
-- --< Header >-- {{{

{-# LANGUAGE MagicHash #-}

{-|

Description : The higher-level interface supporting explicit proof construction.
Copyright   : (c) L. S. Leary, 2024

Similar to the core "NativeCont" interface, the functions in this module require proof tokens to be manually 'evince'd from t'Limit's and composed before being passed explicitly.
To automate this process with GHC's help, use "Control.Continuation.Inferred"
instead.

The advantage of the explicit interface over the inferred one is that it offers a more uniform user experience.
In particular, it's more helpful in the worst case when things aren't coming together easily.
Bad proof arguments are met with good error messages, and typed holes provide precise guidance.

-}

-- }}}

-- --< Imports & Exports >-- {{{

module Control.Continuation.Explicit (

  -- * Scoping #Scoping#
  Scope,
  type (~<)(..),

  -- * Cont #Cont#
  Cont, runCont,
  lower,
  -- ** ContIO #Cont:ContIO#
  ContIO, runContIO,
  runIO, RealWorld,

  -- * Limit #Limit#
  Limit, delimit,
  newLimit, δ, impose,
  evince, sameLimit,
  -- ** Traditional #Limit:Traditional#
  prompt, reset,

  -- * Control Operations #Control_Operations#
  -- $Control_Operations

  -- ** Sunder & Sever #Control_Operations:Sunder_&_Sever#
  sunder, sever,
  -- ** Traditional #Control_Operations:Traditional#
  -- *** Control #Control_Operations:Traditional:Control#
  control0, control,
  -- *** Shift #Control_Operations:Traditional:Shift#
  shift0, shift,
  -- *** Abort #Control_Operations:Traditional:Abort#
  abort0, abort,
  -- *** Return #Control_Operations:Traditional:Return#
  return,

  -- * ST Operations #ST_Operations#
  -- ** STRef #ST_Operations:STRef#
  STRef, newSTRef,
  readSTRef, writeSTRef,
  modifySTRef, modifySTRef',
  -- ** Unsafe #ST_Operations:Unsafe#
  unsafeRunST,

) where

-- base
import Prelude hiding (return)

import Data.STRef (STRef)
import Data.STRef qualified as Base
import Control.Monad.ST (ST)

-- native-cont
import NativeCont (lower#, newLimit#, sunder#, unsafeSTToCont, ioToCont)
import Control.Continuation

-- }}}

-- --< Cont >-- {{{

-- | See 'lower#'.
lower :: p ~< q -> Cont q a -> Cont p a
lower Subscope{proof} = lower# proof

{-|

Run 'IO' in a subscope of the 'RealWorld'.

==== Derivation

\[
  \runIO \app p := \hslower \app p \comp \ioToCont
\]

-}
runIO :: p ~< RealWorld -> IO a -> Cont p a
runIO prw = lower prw . ioToCont

-- }}}

-- --< Limit >-- {{{

-- | See 'newLimit#'.
newLimit :: (forall p. Limit p q a -> Cont q r) -> Cont q r
newLimit k = newLimit# \l -> k (Limit l)

-- | An alias of `newLimit`.
δ :: (forall p. Limit p q a -> Cont q r) -> Cont q r
δ = newLimit

{-|

Delimit a new subscope.

==== Derivation

\[
  \delimit \app k := \delta \lam l {\impose \app l \app \br{k \app l}}
\]

-}
delimit :: (forall p. Limit p q a -> Cont p a) -> Cont q a
delimit k = newLimit \l -> impose l (k l)

-- | A more traditional alias of 'delimit'.
prompt :: (forall p. Limit p q a -> Cont p a) -> Cont q a
prompt = delimit

-- }}}

-- --< Control Operations >-- {{{

{- $Control_Operations

This module provides a zoo of control operations, but there's no reason to get lost in it: the traditional operations are provided /purely for the benefit of those already familiar with them/.
Newcomers need look no further than [Control Operations / Sunder & Sever]("Control.Continuation.Explicit#g:Control_Operations:Sunder_-38-_Sever").

-}

-- --< Sunder & Sever >-- {{{

-- | See 'sunder#'.
sunder
  :: p ~< q -> Limit q r a {- ^ -}
  -> ((Cont p b -> Cont q a) -> Cont r a) -> Cont p b
sunder Subscope{proof} (Limit l) = sunder# proof l

{-|

Sever the continuation at the t'Limit', capturing it together with all it encloses.
As such, the capture is reified at @Cont p b -> Cont r a@.

==== Relatives

 - \( \F - + \)
 - @spawn@ controllers
 - 'shift0'

==== Reduction Semantics

\[
  {\E}_1 \sq{\impose \app l \app {\E}_2 \sq{\sever \app p \app l \app h}}
    \step^*
  {\E}_1 \sq{h \app \lam x {\impose \app l \app {\E}_2 \sq x}}
\]

==== Derivation

\[
  \sever \app p \app l \app f
    := \sunder \app p \app l \app \lam k {
      f \app \br{\impose \app l \comp k}
    }
\]

-}
sever
  :: p ~< q -> Limit q r a {- ^ -}
  -> ((Cont p b -> Cont r a) -> Cont r a) -> Cont p b
sever pq l f = sunder pq l \k -> f (impose l . k)

-- }}}

-- --< Traditional / Control >-- {{{

-- | A more traditional alias of 'sunder'.
control0
  :: p ~< q -> Limit q r a {- ^ -}
  -> ((Cont p b -> Cont q a) -> Cont r a) -> Cont p b
control0 = sunder

{-|

Abortively capture the continuation shy of the t'Limit', hence reifying it at @Cont p b -> Cont q a@.

==== Relatives

 - \( \F + - \)

==== Reduction Semantics

\[
  {\E}_1 \sq { \impose \app l \app {\E}_2 \sq{\control \app p \app l \app h} }
    \step^*
  {\E}_1 \sq { \impose \app l \app \br{h \app \lam x {{\E}_2 \sq x}} }
\]

==== Derivation

\[
  \control \app p \app l \app f
    := \control_0 \app p \app l \app \br{\impose \app l \comp f}
\]

-}
control
  :: p ~< q -> Limit q r a {- ^ -}
  -> ((Cont p b -> Cont q a) -> Cont q a) -> Cont p b
control pq l f = control0 pq l (impose l . f)

-- }}}

-- --< Traditional / Shift >-- {{{

-- | A more traditional alias of 'sever'.
shift0
  :: p ~< q -> Limit q r a {- ^ -}
  -> ((Cont p b -> Cont r a) -> Cont r a) -> Cont p b
shift0 = sever

{-|

Divide the t'Limit' in two, abortively capturing the liberated portion of the continuation.
As such, the capture is that of 'shift0' whereas the working scope is that of 'control'.

==== Relatives

 - \( \F + + \)

==== Reduction Semantics

\[
  {\E}_1 \sq { \impose \app l \app {\E}_2 \sq{\shift \app p \app l \app h} }
    \step^*
  {\E}_1 \sq {
    \impose \app l \app \br{h \app \lam x {\impose \app l \app {\E}_2 \sq x}}
  }
\]

==== Derivation

\[
  \shift \app p \app l \app f
    := \shift_0 \app p \app l \app \br{\impose \app l \comp f}
\]

-}
shift
  :: p ~< q -> Limit q r a {- ^ -}
  -> ((Cont p b -> Cont r a) -> Cont q a) -> Cont p b
shift pq l f = shift0 pq l (impose l . f)

-- }}}

-- --< Traditional / Abort >-- {{{

{-|

Abort all the way to the t'Limit'.

==== Reduction Semantics

\[
  {\E}_1 \sq{\impose \app l \app {\E}_2 \sq{\abort_0 \app p \app l \app e}}
    \step^*
  {\E}_1 \sq e
\]

==== Derivation

\[
  \abort_0 \app p \app l := \control_0 \app p \app l \comp \const
\]

-}
abort0 :: p ~< q -> Limit q r a -> Cont r a -> Cont p b
abort0 pq l = control0 pq l . const

{-|

Abort shy of the t'Limit'.

==== Reduction Semantics

\[
  {\E}_1 \sq{\impose \app l \app {\E}_2 \sq{\abort \app p \app l \app e}}
    \step^*
  {\E}_1 \sq{\impose \app l \app e}
\]

==== Derivation

\[
  \abort \app p \app l := \control \app p \app l \comp \const
\]

-}
abort :: p ~< q -> Limit q r a -> Cont q a -> Cont p b
abort pq l = control pq l . const

-- }}}

-- --< Traditional / Return >-- {{{

{-|

Conclude the delimited computation by immediately returning a result.

==== Reduction Semantics

\[
  {\E}_1 \sq{\impose \app l \app {\E}_2 \sq{\return \app p \app l \app h}}
    \step^*
  {\E}_1 \sq{\pure \app h}
\]

==== Derivation

\[
  \return \app p \app l := \abort_0 \app p \app l \comp \pure
\]

-}
return :: p ~< q -> Limit q r a -> a -> Cont p b
return pq l = abort0 pq l . pure

-- }}}

-- }}}

-- --< ST Operations >-- {{{

{-|

'Base.readSTRef' for 'Cont'.

==== Derivation

\[
  \readSTRef \app p := \unsafeRunST \app p \comp \Base\qual\readSTRef
\]

-}
readSTRef :: p ~< s -> STRef s a -> Cont p a
readSTRef ps = unsafeRunST ps . Base.readSTRef

{-|

'Base.writeSTRef' for 'Cont'.

==== Derivation

\[
  \writeSTRef \app p \app r
    := \unsafeRunST \app p \comp \Base\qual\writeSTRef \app r
\]

-}
writeSTRef :: p ~< s -> STRef s a -> a -> Cont p ()
writeSTRef ps r = unsafeRunST ps . Base.writeSTRef r

{-|

'Base.modifySTRef' for 'Cont'.

==== Derivation

\[
  \modifySTRef \app p \app r
    := \unsafeRunST \app p \comp \Base\qual\modifySTRef \app r
\]

-}
modifySTRef :: p ~< s -> STRef s a -> (a -> a) -> Cont p ()
modifySTRef ps r = unsafeRunST ps . Base.modifySTRef r

{-|

'Base.modifySTRef'' for 'Cont'.

==== Derivation

\[
  \modifySTRef' \app p \app r
    := \unsafeRunST \app p \comp \Base\qual\modifySTRef' \app r
\]

-}
modifySTRef' :: p ~< s -> STRef s a -> (a -> a) -> Cont p ()
modifySTRef' ps s = unsafeRunST ps . Base.modifySTRef' s


{-|

The existence of @lazyToStrictST@ is what makes this function unsafe.
Only __strict__ 'ST' actions can be safely run in 'Cont'.

==== Derivation

\[
  \unsafeRunST \app p := \hslower \app p \comp \unsafeSTToCont
\]

-}
unsafeRunST :: p ~< s -> ST s a -> Cont p a
unsafeRunST ps = lower ps . unsafeSTToCont

-- }}}

