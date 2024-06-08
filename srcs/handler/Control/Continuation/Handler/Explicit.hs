
-- --< Header >-- {{{

{-|

Description : The explicit interface of /native-cont:handler/.
Copyright   : (c) L. S. Leary, 2024

The explicit interface of /native-cont:handler/.

-}

-- }}}

-- --< Imports & Exports >-- {{{

module Control.Continuation.Handler.Explicit (

  Scope,

  -- * Handler #Handler#

  -- ** Monomorphic #Handler:Monomorphic#
  Handler,
  evinceH, limitH,
  install, yield,

  -- ** Polymorphic #Handler:Polymorphic#
  PolyHandler,
  evinceP, limitP,
  installP, yieldP,

) where

-- base
import Data.Coerce (coerce)

-- native-cont
import Control.Continuation.Explicit (Scope, type (~<), Cont, Limit, sever)

-- native-cont:handler
import NativeCont.Handler.Internal (Handler(..), K(..), PolyHandler(..))
import Control.Continuation.Handler

-- }}}

-- --< Handler / Monomorphic >-- {{{

-- | Install a 'yield'-handler with access to the continuation up to the 'Limit'.
install
  :: Limit p q a {- ^ -}
  -> (forall o. o ~< p -> x -> (Cont o y -> Cont q a) -> Cont q a)
  -> Handler p q x y a
install l handler = Handler{ poly = installP l (coerce handler) }

{- |

Yield an @x@ to an enclosing t'Handler' and receive a @y@ in turn.

==== Reduction Semantics

\[
\declare{yield}
\declare{install}
  {\E}_1 \sq{\impose \app l \app {\E}_2 \sq{\yield \app p \app {\left( \install \app l \app h_1 \right)} \app h_2}}
    \step^*
  {\E}_1 \sq{h_1 \app p \app h_2 \app \lam x {\impose \app l \app {\E}_2 \sq x}}
\]

-}
yield :: p ~< q -> Handler q r x y a -> x -> Cont p y
yield pq sz x = coerce (yieldP pq (poly sz) (K x))

-- }}}

-- --< Handler / Polymorphic >-- {{{

-- | Install a 'yieldP'-handler with access to the continuation up to the 'Limit'.
installP
  :: Limit p q a {- ^ -}
  -> ( forall o x
     . o ~< p -> f o x -> (Cont o (g o x) -> Cont q a) -> Cont q a
     )
  -> PolyHandler p q f g a
installP limit handler = PolyHandler{limit,handler}

{- |

Yield an @f p x@ to an enclosing t'PolyHandler' and receive a @g p x@ in turn.

==== Reduction Semantics

\[
  {\E}_1 \sq{\impose \app l \app {\E}_2 \sq{\yield_P \app p \app {\left( \install_P \app l \app h_1 \right)} \app h_2}}
    \step^*
  {\E}_1 \sq{h_1 \app p \app h_2 \app \lam x {\impose \app l \app {\E}_2 \sq x}}
\]

-}
yieldP
  :: p ~< q -> PolyHandler q r f g a {- ^ -}
  -> f p x -> Cont p (g p x)
yieldP pq PolyHandler{limit,handler} = sever pq limit . handler pq

-- }}}

