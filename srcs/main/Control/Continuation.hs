
-- --< Header >-- {{{

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# LANGUAGE
  MagicHash, UnboxedTuples,
  QuantifiedConstraints, UndecidableInstances, FunctionalDependencies
#-}

{-|

Description : The inference-agnostic fragment of the higher-level interface.
Copyright   : (c) L. S. Leary, 2024

Proof tokens; their reflection and reification; limits and basic operations—all /lifted/ for convenience.

 - Unlifted interface: "NativeCont"

This module contains only the fragment of the higher-level interface that is agnostic as to the choice of proof inference or explicit proof construction.

 - Explicit interface: "Control.Continuation.Explicit"
 - Inferred interface: "Control.Continuation.Inferred"

The above both re-export the relevant portions of this module, so there's no reason to import it directly unless you wish to mix and match styles:

> import Control.Continuation
> import Control.Continuation.Explicit qualified as X
> import Control.Continuation.Inferred qualified as I

-}

-- }}}

-- --< Imports & Exports >-- {{{

module Control.Continuation (

  -- * Scoping #Scoping#
  Scope,
  -- ** Proof Tokens #Scoping:Proof_Tokens#
  type (~<)(..),
  -- ** Proof Inference #Scoping:Proof_Inference#
  type (<|),
  auto, reflect,

  -- * Cont #Cont#
  Cont, runCont,

  -- ** ContIO #Cont:ContIO#
  ContIO, runContIO,
  RealWorld,

  -- * Limit #Limit#
  Limit(..),
  impose, evince,
  sameLimit,
  -- ** Traditional #Limit:Traditional#
  reset,

  -- * ST Operations #ST_Operations#
  newSTRef,

) where

-- base
import Prelude hiding (id, (.))

import GHC.Exts (withDict)

import Unsafe.Coerce (unsafeCoerce)

import Data.Type.Equality ((:~:)(..))
import Data.Type.Coercion (Coercion, TestCoercion(..))
import Data.Functor ((<&>))
import Data.Maybe (isJust)
import Data.STRef (STRef)
import Data.STRef qualified as Base
import Control.Monad.ST (RealWorld)
import Control.Category (Category(..))

-- native-cont
import NativeCont

-- }}}

-- --< Scoping >-- {{{

-- | See 'NativeCont.~~<'.
data p ~< q = Subscope{ proof :: {-# UNPACK #-} !(p ~~< q) }

-- | Trivial.
instance Eq (p ~< q) where
  _ == _ = True

-- | Provides reflexivity and transitivity.
instance Category (~<) where
  id      = Subscope{ proof = refl (# #) }
  qr . pq = Subscope{ proof = proof qr ~ proof pq }


class Delimited p q | p -> q where
  auto_ :: p ~< q

-- See: https://discourse.haskell.org/t/trials-tribulations-for-transitivity (though note that some things were simplified or renamed for that post)
class    (forall z. r y z => r x z) => Yoneda r x y
instance (forall z. r y z => r x z) => Yoneda r x y

-- | \( \sub \) in constraint form.
--   All necessary proofs can be inferred so long as all enclosing t'Limit's are 'reflect'ed.
type (<|) = Yoneda Delimited

-- | Infer and reify a proof of \( p \sub q \).
auto :: forall p q. p <| q => p ~< q
auto = withDict @(Delimited q q) id auto_

data Dict c = c => Dict

-- | Reflect a proof to support inference.
--   In safest usage, only a proof 'evince'd directly from a t'Limit' is @reflect@ed, and only a single time.
--   Further @reflect@ions may result in compilation errors during inference.
reflect :: forall p q r. p ~< q -> (p <| q => r) -> r
reflect !_ r = case sadMagic of
  Dict -> r
 where
  -- `<|` has no methods of its own, only a quantified `Delimited` superclass.
  -- Since the `auto_` method of `Delimited` is ultimately phantom in both type parameters, this unsafe coercion should not pose any actual danger, though it does disrepect my abstraction barriers.
  sadMagic :: Dict (p <| q)
  sadMagic = unsafeCoerce (Dict @(p <| p))

-- }}}

-- --< Cont >-- {{{

-- | A specialisation of 'Cont' that may perform IO.
type ContIO = Cont RealWorld

-- | Run @ContIO@ in IO.
runContIO :: ContIO a -> IO a
runContIO = contToIO

-- }}}

-- --< Limit >-- {{{

-- | See 'Limit#'.
data Limit p q a = Limit {-# UNPACK #-} !(Limit# p q a)

-- | Since @Limit@ is singletonian, this instance is trivial.
--   See 'sameLimit' for something useful.
instance Eq (Limit p q a) where
  l1 == l2 = isJust (l1 `sameLimit` l2)

-- | Since @Limit@ is singletonian, this instance is almost trivial.
--   See 'sameLimit' for something more useful.
instance TestCoercion (Limit p q) where
  l1 `testCoercion` l2 = l1 `sameLimit` l2 <&> \(_, _, co) -> co

-- | See 'impose#'.
impose :: Limit p q a -> Cont p a -> Cont q a
impose (Limit l) = impose# l

-- | See 'evince#'.
evince :: Limit p q a -> p ~< q
evince (Limit l) = Subscope{ proof = evince# l }

-- | See 'sameLimit#'.
sameLimit
  :: Limit o q a -> Limit p r b
  -> Maybe (o :~: p, q :~: r, Coercion a b)
Limit l1 `sameLimit` Limit l2 = l1 `sameLimit#` l2

-- | A more traditional alias of 'impose'.
reset :: Limit p q a -> Cont p a -> Cont q a
reset = impose

-- }}}

-- --< ST Operations >-- {{{

{-|

'Base.newSTRef' for 'Cont'.

Unlike the other operations which deal in 'STRef's from any superscope, @newSTRef@ creates references for the /current/ scope.
This is simply for convenience—to avoid the ambiguity that results from being too polymorphic.
To create an 'STRef' for a superscope, use in combination with @lower@.

==== Derivation

\[
  \newSTRef := \unsafeSTToCont \comp \Base\qual\newSTRef
\]

-}
newSTRef :: a -> Cont p (STRef p a)
newSTRef = unsafeSTToCont . Base.newSTRef

-- }}}

