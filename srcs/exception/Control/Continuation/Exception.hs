
-- --< Header >-- {{{

{-# LANGUAGE DataKinds, GADTs, UndecidableInstances #-}

{-|

Description : Checked exceptions implemented via /native-cont/.
Copyright   : (c) L. S. Leary, 2024

Checked exceptions.

-}

-- }}}

-- --< Imports & Exports >-- {{{

module Control.Continuation.Exception (

  Scope,

  -- * Checked Exceptions #Checked_Exceptions#

  -- ** In Cont #Checked_Exceptions:In_Cont#
  Checked,
  catchC, tryC,
  throwC,

  -- ** In Except #Checked_Exceptions:In_Except#
  Except, ExceptIO,
  runExcept, liftCont,
  catch, try,
  type (<:), throw,

) where

-- base
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO(..))

-- transformers
import Control.Monad.Trans.Reader (ReaderT(..))

-- native-cont
import Control.Continuation.Inferred
  (Scope, type (<|), Cont, lower, runIO, RealWorld, delimit, abort0)

-- }}}

-- --< Checked Exceptions / In Cont >-- {{{

-- | A @Checked p e@ witnesses that in scope @p@, @e@ is a checked exception.
newtype Checked p e = Checked{ throw_ :: forall a. e -> Cont p a }

{- | Establish a subscope which checks for @e@ and attempt a computation, recovering from failure with the supplied handler.

==== Reduction Semantics

\( \declare{catch} \catch_C \app \br{\lam {\p\p\cdot\p\p} \cdots} \app h \) is treated as a /check binder/ under which execution continues. \[
  {\E} \sq{\catch_C \app \br{\lam x {\pure \app h_1}} \app h_2}
    \step^*
  {\E} \sq{\pure \app h_1}
\]

-}
catchC
  :: (forall p. p <| q => Checked p e -> Cont p a) {- ^ -}
  -> (e -> Cont q a)
  -> Cont q a
catchC scope handle = delimit \l ->
  scope Checked{ throw_ = abort0 l . handle }

{- | Establish a subscope which checks for @e@ and attempt a computation, producing @Left e@ on failure and @Right a@ on success.

==== Reduction Semantics

\[
\declare{try}
\declare{Left}
\declare{Right}
  {\E} \sq{\try_C \app \lam x {\pure \app h}}
    \step^*
  {\E} \sq{\pure \app \br{\Right \app h}}
\]

==== Derivation

\[
\declare{fmap}
  \try_C \app f
    := \catch_C \app \br{\fmap \app \Right \comp f}
                \app \br{\pure \comp \Left}
\]

-}
tryC
  :: (forall p. p <| q => Checked p e -> Cont p a) {- ^ -}
  -> Cont q (Either e a)
tryC scope = catchC (fmap Right . scope) (pure . Left)

{- | Provide a proof that @e@ will be caught and hence throw it.

==== Reduction Semantics

\[
\declare{throw}
  {\E}_1 \sq{\catch_C \app \br{ \lam x {{\E}_2 \sq{\throw_C \app x \app h_1}} } \app h_2}
    \step^*
  {\E}_1 \sq{h_2 \app h_1}
\]

-}
throwC :: p <| q => Checked q e -> e -> Cont p a
throwC Checked{throw_} e = lower (throw_ e)

-- }}}

-- --< Checked Exceptions / In Except >-- {{{

data Exceptions p es where
  Nil  :: Exceptions p '[]
  Cons :: p <| q
       => Checked p e -> Exceptions q es -> Exceptions p (e:es)

type ExceptRep p es = ReaderT (Exceptions p es) (Cont p)

-- | A monad for checked exceptions.
newtype Except p es a
  = Except{ unExcept :: Exceptions p es -> Cont p a }
  deriving (Functor, Applicative, Monad, MonadFix)
    via ExceptRep p es

type ExceptIO = Except RealWorld

instance p <| RealWorld => MonadIO (Except p es) where
  liftIO = liftCont . runIO

runExcept :: Except p '[] a -> Cont p a
runExcept act = unExcept act Nil

liftCont :: Cont p a -> Except p es a
liftCont p = Except \_ -> p

-- | Exception /inclusion/ constraint.
type (<:) = (<::)

class e <:: es where
  project :: Exceptions p es
          -> (forall q. p <| q => Checked q e -> r) -> r

instance {-# OVERLAPPING #-} e <:: (e:es) where
  project (Cons h _ ) k = k h

instance {-# OVERLAPPABLE #-} e <:: es => e <:: (d:es) where
  project (Cons _ hs) k = project hs k

catch
  :: (forall p. p <| q => Except p (e:es) a) {- ^ -}
  -> (e -> Except q es a)
  -> Except q es a
catch act handle = Except \es -> catchC
  (\x -> unExcept  act       (Cons x es))
  (\e -> unExcept (handle e)         es )

try
  :: (forall p. p <| q => Except p (e:es) a) {- ^ -}
  -> Except q es (Either e a)
try act = catch (Right <$> act) (pure . Left)

throw :: e <: es => e -> Except p es a
throw e = Except \xs -> project xs \x ->
  throwC x e

-- }}}

