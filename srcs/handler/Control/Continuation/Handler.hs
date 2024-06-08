
-- --< Header >-- {{{

{-# LANGUAGE DataKinds #-}

{-|

Description : The inference-agnostic fragment of /native-cont:handler/.
Copyright   : (c) L. S. Leary, 2024

The inference-agnostic fragment of /native-cont:handler/.

-}

-- }}}

-- --< Imports & Exports >-- {{{

module Control.Continuation.Handler (

  -- * Handler #Handler#

  -- ** Monomorphic #Handler:Monomorphic#
  Handler,
  limitH, evinceH,

  -- ** Polymorphic #Handler:Polymorphic#
  PolyHandler,
  limitP, evinceP,

) where

-- native-cont
import Control.Continuation (type (~<), Limit, evince)

-- native-cont:handler
import NativeCont.Handler.Internal (Handler(poly), PolyHandler(limit))

-- }}}

-- --< Handler / Monomorphic >-- {{{

-- | Extract the 'Limit' of a 'Handler'.
limitH :: Handler p q x y a -> Limit p q a
limitH = limit . poly

-- | 'evince' for 'Handler'.
evinceH :: Handler p q x y a -> p ~< q
evinceH = evinceP . poly

-- }}}

-- --< Handler / Polymorphic >-- {{{

-- | Extract the 'Limit' of a 'PolyHandler'.
limitP
  :: PolyHandler p q f g a {- ^ -}
  -> Limit p q a
limitP = limit

-- | 'evince' for 'PolyHandler'.
evinceP
  :: PolyHandler p q f g a {- ^ -}
  -> p ~< q
evinceP = evince . limit

-- }}}

