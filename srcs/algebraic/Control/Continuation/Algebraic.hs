
-- --< Header >-- {{{

{-# LANGUAGE NoStarIsType, DataKinds, GADTs, UndecidableInstances #-}
{-# LANGUAGE UnboxedTuples #-}

{-|

Description : Algebraic effects implemented via /native-cont:handler/.
Copyright   : (c) L. S. Leary, 2024

Algebraic effects.

-}

-- }}}

-- --< Imports & Exports >-- {{{

module Control.Continuation.Algebraic (

  Scope,

  -- * Algebraic Effects #Algebraic_Effects#
  -- $algebraicity

  -- ** In Cont #Algebraic_Effects:In_Cont#
  Effect,
  newEffectC, effC,

  -- ** In Eff #Algebraic_Effects:In_Eff#
  Eff, EffIO, runEff,
  liftCont, withRunInCont,
  newEffect, eff,

  -- * Signatures #Signatures#

  -- ** Combination #Signatures:Combination#
  type (+), (|+|),
  type (*), (|*|), prod,
  type (.), (|.|),

  -- ** Transformation #Signatures:Transformation#
  inEff,

  -- ** State #Signatures:State#
  Reader(..), runReader, ask, asks,
  Writer(..), runWriter, tell, writer,
  State(..),  runState, get, put, modify, state,

  -- ** Non-Determinism #Signatures:Non-Determinism#
  Fail(..), runFail, runFailA,
  Choose(..), runChoose, runChooseA, (|||),
  NonDet(..), runNonDet, runNonDetA,

  -- * Appendix #Appendix#
  -- $Appendix

) where

-- base
import GHC.Exts (TYPE)

import Data.Kind (Type)
import Data.Coerce (coerce)
import Control.Applicative (Alternative(..))
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.IO.Class (MonadIO(..))

-- transformers
import Control.Monad.Trans.Reader (ReaderT(..))

-- native-cont
import Control.Continuation.Inferred

-- native-cont:handler
import Control.Continuation.Handler.Inferred

-- }}}

-- --< Algebraic Effects: In Cont >-- {{{

{- $algebraicity #algebraicity#

__Definition__: An effect \( op \) is /algebraic/ iff:

  1. \( op \)@ :: forall a. S (M a) -> M a@ for some functor @S@ and monad @M@.
  2. \( \forall x, k: op \app x \bind k = op \app (x \mapping (\bind k)) \)

-}

-- | An @Effect p e@ witnesses that algebraic effects of signature @e@ are supported in scope @p@.
data Effect p e = forall q a.
  Effect {-# UNPACK #-} !(PolyHandler p q (In e) Out a)

newtype In e p a = In (e (Cont p a))
newtype Out  p a = Out           a

{- |

Supply \( op \)—an @e@ algebra on @Cont q a@—and obtain a corresponding algebraic effect handle in a new subscope.
Note that \( op \) itself need not be algebraic in the precise sense of [algebraicity]("Control.Continuation.Algebraic#algebraicity"); see [Appendix]("Control.Continuation.Algebraic#g:Appendix") for detail.

==== Reduction Semantics

\( \declare{newEffect} \newEffect_C \app op \app \lambda \) is treated as an /effect binder/ under which execution continues. \[
  {\E} \sq{\newEffect_C \app op \app \lam x {\pure \app h}}
    \step^*
  {\E} \sq{\pure \app h}
\]

-}
newEffectC
  :: Functor e
  => (e (Cont q a) -> Cont q a) {- ^ -}
  -> (forall p. p <| q => Effect p e -> Cont p a)
  -> Cont q a
newEffectC op scope = delimit \l ->
  scope . Effect $ installP l \(In s) k ->
    op (k . coerce <$> s)

{- |

Prove that @e@-effects are supported in the current scope in order to execute them.

==== Reduction Semantics

\[
\declare{eff}
  {\E}_1 \sq{ \newEffect_C \app op \app \lam x {{\E}_2 \sq{\eff_C \app x \app \sigma}} }
    \step^*
  {\E}_1 \sq{op \app \br{ \sigma \mapping \lam y {\newEffect_C \app op \app \lam x {{\E}_2 \sq y}} }}
\]

-}
effC :: p <| q => Effect q e -> e (Cont p a) -> Cont p a
effC (Effect h) s = coerce (yieldP h (In s))

-- }}}

-- --< Algebraic Effects: As Eff >-- {{{

data Effects p es where
  Nil  :: Effects p '[]
  Cons :: p <| q => Effect p e -> Effects q es -> Effects p (e:es)

type EffRep p es = ReaderT (Effects p es) (Cont p)

-- | A dedicated monad for algebraic effects.
newtype Eff p es a = Eff{ unEff :: Effects p es -> Cont p a }
  deriving (Functor, Applicative, Monad, MonadFix)
    via EffRep p es

type EffIO = Eff RealWorld

instance p <| RealWorld => MonadIO (Eff p es) where
  liftIO = liftCont . runIO

runEff :: Eff p '[] a -> Cont p a
runEff act = unEff act Nil

-- | Unlift 'Cont' in t'Eff' à la @withRunInIO@.
withRunInCont
  :: ((forall x. Eff p es x -> Cont p x) -> Cont p a) {- ^ -}
  -> Eff p es a
withRunInCont k = Eff \es -> k (`unEff` es)

liftCont :: Cont p a -> Eff p es a
liftCont p = withRunInCont \_ -> p

type (<:) = (<::)

class e <:: es where
  project :: Effects p es -> (forall q. p <| q => Effect q e -> r) -> r

instance {-# OVERLAPPING #-} e <:: (e:es) where
  project (Cons h _ ) k = k h

instance {-# OVERLAPPABLE #-} e <:: es => e <:: (d:es) where
  project (Cons _ hs) k = project hs k

-- | See 'newEffectC'.
newEffect
  :: Functor e
  => (e (Eff q es a) -> Eff q es a) {- ^ -}
  -> (forall p. p <| q => Eff p (e:es) a)
  -> Eff q es a
newEffect op act = Eff \es ->
  newEffectC (flip unEff es . op . fmap liftCont) \e ->
    unEff act (Cons e es)

-- | See 'effC'.
eff :: Functor e => e <: es => e (Eff p es a) -> Eff p es a
eff s = Eff \es -> project es \e ->
  effC e (flip unEff es <$> s)

-- }}}

-- --< Signatures: Combination & Transformation >-- {{{

data (f + g) a = InL (f a) | InR (g a)
  deriving Functor

(|+|) :: (f a -> a) -> (g a -> a) -> (f + g) a -> a
f |+| g = \case
  InL fa -> f fa
  InR ga -> g ga
infixr 1 |+|


data (f * g) a = f a :* g a
  deriving Functor

(|*|) :: Semigroup a => (f a -> a) -> (g a -> a) -> (f * g) a -> a
(|*|) = prod (<>)
infixr 2 |*|

prod :: (a -> b -> c) -> (f c -> a) -> (g c -> b) -> (f * g) c -> c
prod abc fca gcb (fc :* gc) = abc (fca fc) (gcb gc)


newtype (f . g) a = Comp{ getComp :: f (g a) }
  deriving Functor

(|.|) :: Functor f => (f a -> a) -> (g a -> a) -> (f . g) a -> a
f |.| g = f . fmap g . getComp
infixr 3 |.|


inEff
  :: Functor e
  => (e (Cont p a) -> Cont p a) {- ^ -}
  -> (e (Eff p es a) -> Eff p es a)
inEff op ee = withRunInCont \run ->
  op (run <$> ee)

-- }}}

-- --< Signatures: State >-- {{{

type Reader :: TYPE rr -> Type -> Type
newtype Reader r a = Ask{ unAsk :: r -> a }

instance Functor (Reader r) where
  fmap f (Ask g) = Ask (f . g)

runReader :: r -> Reader r a -> a
runReader r (Ask f) = f r

ask :: Reader r <: es => Eff p es r
ask = asks id

asks :: Reader r <: es => (r -> a) -> Eff p es a
asks f = eff (Ask (pure . f))


data Writer w a = Tell w a
  deriving Functor

runWriter
  :: STRef p ws -> (ws -> w -> ws)
  -> Writer w (Cont p a) -> Cont p a
runWriter ws (|>) (Tell w ca) = modifySTRef' ws (|> w) *> ca

writer :: Writer w <: es => a -> w -> Eff p es a
writer x w = eff (Tell w (pure x))

tell :: Writer w <: es => w -> Eff p es ()
tell = writer ()


type State :: TYPE rr -> Type -> Type
newtype State s a = State{ unState :: s -> (# s, a #) }

instance Functor (State s) where
  fmap f (State g) = State \s -> case g s of
    (# s', x #) -> (# s', f x #)

runState :: STRef p a -> State a (Cont p b) -> Cont p b
runState ref (State f) = do
  s <- readSTRef ref
  case f s of
    (# s', x #) -> writeSTRef ref s' *> x

get :: State a <: es => Eff p es a
get = state \s -> (s, s)

put :: State a <: es => a -> Eff p es ()
put s = modify \_ -> s

modify :: State a <: es => (a -> a) -> Eff p es ()
modify f = state \s -> ((), f s)

state :: State a <: es => (a -> (b, a)) -> Eff p es b
state f = eff $ State \s -> case f s of
  (x, s') -> (# s', pure x #)

-- }}}

-- --< Signatures: Non-Determinism >-- {{{

data Fail a = Fail String
  deriving Functor

runFail :: Monoid a => Fail a -> a
runFail = mempty

runFailA :: Applicative f => a -> Fail (f a) -> f a
runFailA x _ = pure x

instance Fail <: es => MonadFail (Eff p es) where
  fail = eff . Fail


data Choose a = Choose a a
  deriving Functor

runChoose :: Semigroup a => Choose a -> a
runChoose (Choose l r) = l <> r

runChooseA :: Applicative f => (a -> a -> a) -> Choose (f a) -> f a
runChooseA fuse (Choose l r) = liftA2 fuse l r

(|||) :: Choose <: es => Eff p es a -> Eff p es a -> Eff p es a
l ||| r = eff (Choose l r)


newtype NonDet a = NonDet{ det :: (Fail + Choose) a }
  deriving Functor

runNonDet :: Monoid a => NonDet a -> a
runNonDet = (runFail |+| runChoose) . det

runNonDetA :: Applicative f => a -> (a -> a -> a) -> NonDet (f a) -> f a
runNonDetA x fuse = (runFailA x |+| runChooseA fuse) . det

instance NonDet <: es => Alternative (Eff p es) where
  empty   = eff (NonDet (InL (Fail "empty")))
  l <|> r = eff (NonDet (InR (Choose l r  )))

-- }}}

-- --< Appendix >-- {{{

{- $Appendix

\( \eff_C \app e_{op} \) is algebraic regardless of the algebraicity of \( op \)
itself.
By extension, the same applies to \( \eff \).

/(for simplicity we erase coercions)/

> effC e s >>= f
>   = effC (Effect h) s >>= f
>   = coerce (yieldP h (In s)) >>= f
>   = yieldP h (In s) >>= f
>   = (\(In s) k -> op (k . coerce <$> s)) (In s) (>>= f)
>   = (\(In s) k -> op (k <$> s)) (In s) (>>= f)
>   = op ((>>= f) <$> s)
>   = op (s <&> (>>= f))

> effC e (s <&> (>>= f))
>   = effC (Effect h) (s <&> (>>= f))
>   = coerce (yieldP h (In (s <&> (>>= f))))
>   = yieldP h (In (s <&> (>>= f)))
>   = (\(In s) k -> op (k . coerce <$> s)) (In (s <&> (>>= f))) id
>   = (\(In s) k -> op (k <$> s)) (In (s <&> (>>= f))) id
>   = op (s <&> (>>= f))
>   = effC e s >>= f

If \( op \) /is/ algebraic, then \( \eff_C \app e_{op} \) recovers \( op \)
precisely:

> effC e s >>= f
>   = op (s <&> (>>= f))
>   = op s >>= f

-}

-- }}}

