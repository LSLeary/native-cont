{-# OPTIONS_HADDOCK hide not-home #-}
{-# LANGUAGE DataKinds #-}

module NativeCont.Handler.Internal (
  Handler(..), K(..),
  PolyHandler(..),
) where

-- base
import Data.Kind (Type)
import Data.Type.Coercion (TestCoercion(..))
import Data.Function (on)

-- native-cont
import Control.Continuation (Scope, Limit, Cont)
import Control.Continuation.Explicit (type (~<))


-- | Like a @Limit p q a@, a @Handler p q x y a@ delimits from @q@ a direct subscope @p@ wherein an @a@ is to be produced.
-- Within @p@, one may 'yield@ an @x@ to the @Handler@ and be supplied a @y@ in turn.
newtype Handler p q x y a = Handler{ poly :: PolyHandler p q (K x) (K y) a }
  deriving (Eq, TestCoercion)

-- | A 'Data.Functor.Const.Const'-like newtype ignoring its last two type parameters.
--   Used to simplify t'PolyHandler' down to t'Handler'.
type K :: Type -> Scope -> Type -> Type
newtype K x p a = K{ unK :: x }


-- | A scope-aware, polymorphic generalisation of t'Handler': within any subscope @r@ of @p@, one may yield an @f r x@ to the @PolyHandler@ and be supplied a @g r x@ in turn.
data PolyHandler p q f g a = PolyHandler
  { limit
      :: {-# UNPACK #-} !(Limit p q a)
  , handler
      :: forall r x
       . r ~< p -> f r x -> (Cont r (g r x) -> Cont q a) -> Cont q a
  }

instance Eq (PolyHandler p q f g a) where
  (==) = (==) `on` limit

instance TestCoercion (PolyHandler p q f g) where
  testCoercion p1 p2 = testCoercion (limit p1) (limit p2)

