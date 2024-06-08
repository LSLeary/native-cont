
-- --< Header >-- {{{

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# LANGUAGE MagicHash #-} -- for haddock

{-|

Description : The higher-level interface supporting implicit proof inference.
Copyright   : (c) L. S. Leary, 2024

This module is a thin wrapper over "Control.Continuation.Explicit" composed almost entirely of applications to 'auto', in order to provide transparent proof inference.
This is very convenient when your program is well structured, such that it may /just work/.
The spell breaks when you err, however, leaving you subject to the wrath of the Glasgow Haskell Compiler.
On such occasions, it's advisable to fall back on the explicit interface.

/Tip: set @-Wno-simplifiable-class-constraints@ in files using this module./

-}

-- }}}

-- --< Imports & Exports >-- {{{

module Control.Continuation.Inferred (

  -- * Scoping #Scoping#
  Scope,
  type (~<)(..),
  type (<|),
  auto, reflect,

  -- * Cont #Cont#
  Cont, runCont,
  lower,

  -- ** ContIO #Cont:ContIO#
  ContIO, runContIO,
  runIO, RealWorld,

  -- * Limit #Limit#
  Limit, delimit,
  newLimit, δ, impose,
  sameLimit,
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
import Control.Monad.ST (ST)

-- native-cont
import Control.Continuation
import Control.Continuation.Explicit qualified as X

-- }}}

-- --< Cont >-- {{{

-- | See 'NativeCont.lower#'.
lower :: p <| q => Cont q a -> Cont p a
lower = X.lower auto

-- | See 'Control.Continuation.Explicit.runIO'.
runIO :: p <| RealWorld => IO a -> Cont p a
runIO = X.runIO auto

-- }}}

-- --< Limit >-- {{{

{- | See 'Control.Continuation.Explicit.delimit'.

==== Derivation

\[
\declare[q]{X}
\declare{reflect}
\declare{evince}
  \delimit \app k := \qX\qual\delimit \app \lam l {
    \reflect \app \br{\evince \app l} \app \br{k \app l}
  }
\]

-}
delimit
  :: (forall p. p <| q => Limit p q a -> Cont p a)
  -> Cont q a
delimit k = X.delimit \l -> reflect (evince l) (k l)

{- | See 'Control.Continuation.Explicit.newLimit'.

==== Derivation

\[
  \newLimit \app k := \qX\qual\newLimit \app \lam l {
    \reflect \app \br{\evince \app l} \app \br{k \app l}
  }
\]

-}
newLimit
  :: (forall p. p <| q => Limit p q a -> Cont q r)
  -> Cont q r
newLimit k = X.newLimit \l -> reflect (evince l) (k l)

-- | An alias of `newLimit`.
δ :: (forall p. p <| q => Limit p q a -> Cont q r)
  -> Cont q r
δ = newLimit

-- | See 'Control.Continuation.Explicit.prompt'.
prompt
  :: (forall p. p <| q => Limit p q a -> Cont p a)
  -> Cont q a
prompt = delimit

-- }}}

-- --< Control Operations >-- {{{

{- $Control_Operations

See [Control Operations]("Control.Continuation.Explicit#g:Control_Operations").

-}

-- --< Sunder & Sever >-- {{{

-- | See 'NativeCont.sunder#'.
sunder
  :: p <| q => Limit q r a {- ^ -}
  -> ((Cont p b -> Cont q a) -> Cont r a) -> Cont p b
sunder = X.sunder auto

-- | See 'Control.Continuation.Explicit.sever'.
sever
  :: p <| q => Limit q r a {- ^ -}
  -> ((Cont p b -> Cont r a) -> Cont r a) -> Cont p b
sever = X.sever auto

-- }}}

-- --< Traditional / Control >-- {{{

-- | See 'Control.Continuation.Explicit.control0'.
control0
  :: p <| q => Limit q r a {- ^ -}
  -> ((Cont p b -> Cont q a) -> Cont r a) -> Cont p b
control0 = sunder

-- | See 'Control.Continuation.Explicit.control'.
control
  :: p <| q => Limit q r a {- ^ -}
  -> ((Cont p b -> Cont q a) -> Cont q a) -> Cont p b
control = X.control auto

-- }}}

-- --< Traditional / Shift >-- {{{

-- | See 'Control.Continuation.Explicit.shift0'.
shift0
  :: p <| q => Limit q r a {- ^ -}
  -> ((Cont p b -> Cont r a) -> Cont r a) -> Cont p b
shift0 = sever

-- | See 'Control.Continuation.Explicit.shift'.
shift
  :: p <| q => Limit q r a {- ^ -}
  -> ((Cont p b -> Cont r a) -> Cont q a) -> Cont p b
shift = X.shift auto

-- }}}

-- --< Traditional / Abort >-- {{{

-- | See 'Control.Continuation.Explicit.abort0'.
abort0 :: p <| q => Limit q r a -> Cont r a -> Cont p b
abort0 = X.abort0 auto

-- | See 'Control.Continuation.Explicit.abort'.
abort :: p <| q => Limit q r a -> Cont q a -> Cont p b
abort = X.abort auto

-- }}}

-- --< Traditional / Return >-- {{{

-- | See 'Control.Continuation.Explicit.return'.
return :: p <| q => Limit q r a -> a -> Cont p b
return = X.return auto

-- }}}

-- }}}

-- --< ST Operations >-- {{{

-- | See 'Control.Continuation.Explicit.readSTRef'.
readSTRef :: p <| s => STRef s a -> Cont p a
readSTRef = X.readSTRef auto

-- | See 'Control.Continuation.Explicit.writeSTRef'.
writeSTRef :: p <| s => STRef s a -> a -> Cont p ()
writeSTRef = X.writeSTRef auto

-- | See 'Control.Continuation.Explicit.modifySTRef'.
modifySTRef :: p <| s => STRef s a -> (a -> a) -> Cont p ()
modifySTRef = X.modifySTRef auto

-- | See 'Control.Continuation.Explicit.modifySTRef''.
modifySTRef' :: p <| s => STRef s a -> (a -> a) -> Cont p ()
modifySTRef' = X.modifySTRef' auto

-- | See 'Control.Continuation.Explicit.unsafeRunST'.
unsafeRunST :: p <| s => ST s a -> Cont p a
unsafeRunST = X.unsafeRunST auto

-- }}}

