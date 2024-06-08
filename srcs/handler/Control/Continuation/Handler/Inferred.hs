
-- --< Header >-- {{{

{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

{-|

Description : The implicit interface of /native-cont:handler/.
Copyright   : (c) L. S. Leary, 2024

The implicit interface of /native-cont:handler/.

-}

-- }}}

-- --< Imports & Exports >-- {{{

module Control.Continuation.Handler.Inferred (

  Scope,

  -- * Handler #Handler#

  -- ** Monomorphic #Handler:Monomorphic#
  Handler,
  limitH,
  install, yield,

  -- ** Polymorphic #Handler:Polymorphic#
  PolyHandler,
  limitP,
  installP, yieldP,

) where

-- native-cont
import Control.Continuation.Inferred
  (Scope, type (<|), auto, reflect, Cont, Limit,)

-- native-cont:handler
import           Control.Continuation.Handler
import qualified Control.Continuation.Handler.Explicit as X

-- }}}

-- --< Handler / Monomorphic >-- {{{

-- | See 'Control.Continuation.Handler.Explicit.install'.
install
  :: Limit p q a {- ^ -}
  -> (forall o. o <| p => x -> (Cont o y -> Cont q a) -> Cont q a)
  -> Handler p q x y a
install l handler = X.install l \pq -> reflect pq handler

-- | See 'Control.Continuation.Handler.Explicit.yield'.
yield :: p <| q => Handler q r x y a -> x -> Cont p y
yield = X.yield auto

-- }}}

-- --< Handler / Polymorphic >-- {{{

-- | See 'Control.Continuation.Handler.Explicit.installP'.
installP
  :: Limit p q a {- ^ -}
  -> ( forall o x
     . o <| p => f o x -> (Cont o (g o x) -> Cont q a) -> Cont q a
     )
  -> PolyHandler p q f g a
installP l handler = X.installP l \pq -> reflect pq handler

-- | See 'Control.Continuation.Handler.Explicit.yieldP'.
yieldP
  :: p <| q => PolyHandler q r f g a {- ^ -}
  -> f p x -> Cont p (g p x)
yieldP = X.yieldP auto

-- }}}

