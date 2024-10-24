
-- --< Header >-- {{{

{-# LANGUAGE MagicHash, UnboxedTuples, UnliftedNewtypes, DataKinds #-}

{-|

Description : The low-level core of /native-cont/.
Copyright   : (c) L. S. Leary, 2024

This module constitutes the minimal complete public interface of /native-cont/.
Its purpose is to be the simplest possible foundation for the "Control.Continuation"⁎ modules without compromising on safety or efficiency.
What it lacks instead is the convenience of the higher-level interfaces.

Recommended watching: [Delimited Continuations, Demystified](https://www.youtube.com/watch?v=TE48LsgVlIU) by Alexis King (1:03:04).

-}

-- }}}

-- --< Imports & Exports >-- {{{

module NativeCont (

  -- * Scoping #Scoping#
  Scope,
  -- ** Proof Tokens #Scoping:Proof_Tokens#
  type (~~<),
  refl, (~), anti,

  -- * Cont #Cont#
  Cont, runCont,
  lower#,
  -- ** IO #Cont:IO#
  contToIO, ioToCont,
  -- ** Unsafe #Cont:Unsafe#
  unsafeSTToCont,

  -- * Limit #Limit#
  Limit#, newLimit#,
  impose#, evince#,
  sameLimit#,

  -- * Sunder #Sunder#
  sunder#,

  -- * About #About#

  -- ** Safety #About:Safety#
  -- $Safety

  -- *** Purity #About:Safety:Purity#
  -- $Purity

  -- *** Well-Scopedness #About:Safety:Well-Scopedness#
  -- $Well-Scopedness

  -- *** Threading Invariants #About:Safety:Threading_Invariants#
  -- $Threading_Invariants

  -- *** IO Interface Preservation #About:Safety:IO_Interface_Preservation#
  -- $IO_Interface_Preservation

  -- ** This Documentation #About:This_Documentation#

  -- *** Derivations #About:This_Documentation:Derivations#
  -- $Derivations

  -- *** Reduction Semantics #About:This_Documentation:Reduction_Semantics#
  -- $Reduction_Semantics

) where

-- base
import GHC.Exts qualified as GHC (control0#)
import GHC.Exts
  ( PromptTag#, newPromptTag#, prompt#
  , UnliftedType, ZeroBitType
  , isTrue#, unsafePtrEquality#, State#
  )
import GHC.IO (IO(..))
import GHC.ST (ST(..))

import Unsafe.Coerce (unsafeCoerce, unsafeCoerce#)

import Data.Kind (Type, )
import Data.Coerce (coerce)
import Data.Type.Equality ((:~:)(..))
import Data.Type.Coercion (Coercion(..))
import Data.Functor ((<&>))
import Control.Monad.ST (runST, RealWorld)
import Control.Monad.Fix (MonadFix(..))

-- }}}

{-        ╭─────────────────────────────────────────────────────────╮
          │ ¡WARNING! ¡Any function named prim* or *Prim is unsafe! │
          ╰─────────────────────────────────────────────────────────╯         -}

-- --< Scoping >-- {{{

{- |

The kind of /scopes/.

/Hack: @Scope@ re-exports carry \( \LaTeX \) macros to haddocks in need./

\[
% -- --< LaTeX Macros >-- {{{
%
% Layout
\newcommand{\p}{ \kern0.5pt }
\newcommand{\n}{ \kern-0.5pt }
%
%
% Haskell
\newcommand{\code}[1]{\texttt{#1}}
%
% INCOMPATIBILITY: MathJax doesn't support \expandafter
%
% LaTeX
%\newcommand{\declare}[2][]{
%  \expandafter\newcommand\csname #1#2\endcsname{\code{#2}}
%}
%\newcommand{\redeclare}[2][]{
%  \expandafter\renewcommand\csname #1#2\endcsname{\code{#2}}
%}
%
% MathJax
\newcommand{\declare}[2][]{ \newcommand{#1#2}{\code{#2}} }
\newcommand{\redeclare}[2][]{ \renewcommand{#1#2}{\code{#2}} }
%
\newcommand{\Hask}{\text{Hask}}
\newcommand{\unit}{\code{()}}
%
% INCOMPATIBILITY: MathJax doesn't want to escape #.
%
% MathJax
\newcommand{\hash}{\code{#}}
%
% LaTeX
%\newcommand{\hash}{\code{\#}}
%
\renewcommand{\|}{\mathpunct{\,|}}
\newcommand{\app}{\p\p\p\p\p}
\newcommand{\comp}{\circ}
\newcommand{\lam}[2]{\lambda #1 . \, #2}
\newcommand{\del}[2]{\delta  #1 . \, #2}
\newcommand{\bind}{>\n\n\n\n\n\n\n>\n\n\n\n\n\n=}
\newcommand{\mapping}{<\n\n\n\n\n\n\n\&\n\n\n\n\n\n\n>}
\declare{const}
\declare{pure}
\declare{Base}
%
% INCOMPATIBILITY: Spacing around . seems to differ greatly in MathJax.
%
% LaTeX
%\newcommand{\qual}{.}
%
% MathJax
\newcommand{\qual}{\p.\n\n\n}
%
% ST
\declare{newSTRef}
\declare{readSTRef}
\declare{writeSTRef}
\declare{modifySTRef}
%
% Delimited Continuations
\newcommand{\sub}{\leq_{enc}}
\newcommand{\redAx}{ \operatorname*{\mathrel{\longrightarrow}} }
\newcommand{\Not}[1]{\n\rlap{\,\,\,\,/} #1}
\newcommand{\step}{ \operatorname*{\mathrel{\longmapsto}} }
\newcommand{\F}[2]{\sideset{^{#1\n}}{^{#2}}{
  \operatorname{\mathcal F}
}}
\newcommand{\E}{\operatorname*{\mathit E}}
\newcommand{\br}[1]{{\left(#1\right)}}
\newcommand{\sq}[1]{{\left[#1\right]}}
\newcommand{\hole}{\bullet}
\newcommand{\eval}{ \operatorname*{\mathrm{eval}} }
\newcommand{\proj}{\operatorname*{\pi}}
\newcommand{\parto}{\rightharpoonup}
\declare{Cont}
\declare{runCont}
\declare[hs]{lower}
\declare{newLimit}
\declare{impose}
\declare{delimit}
\declare{sunder}
\declare{sever}
\declare{control}
\declare{shift}
\declare{abort}
\declare{return}
%
% Base Monad Coercions
\declare{IO}
\declare{contToIO}
\declare{ioToCont}
\declare{unsafeSTToCont}
\declare{runIO}
\declare{unsafeRunST}
%
% }}}
\]

-}
type Scope = Type

-- --< Proof Tokens >-- {{{

-- | Enclosure induces a partial order \( \sub \) on scopes, which we call the /subscoping/ relation. A @p ~~< q@ is witness to \( p \sub q \): it constitutes a proof that @p@ is a subscope of @q@.
type role (~~<) nominal nominal
type (~~<) :: Scope -> Scope -> ZeroBitType
newtype p ~~< q = UnsafeSubScopeProof# (# #)

-- | Subscoping is /reflexive/: \[
--     \forall p:  p \sub p
--   \]
refl :: (# #) -> p ~~< p
refl = UnsafeSubScopeProof#

-- | Subscoping is /transitive/: \[
--     \forall p, q, r:  p \sub q  \wedge  q \sub r  \implies  p \sub r
--   \]
(~) :: q ~~< r -> p ~~< q -> p ~~< r
!_ ~ !_ = UnsafeSubScopeProof# (# #)

-- | Subscoping is /anti-symmetric/: \[
--     \forall p, q:  p \sub q  \wedge  q \sub p  \implies  p = q
--   \]
anti :: forall p q. p ~~< q -> q ~~< p -> p :~: q
anti !_ !_ = unsafeCoerce (Refl :: p :~: p)

-- }}}

-- }}}

-- --< Internal: Prim >-- {{{

-- An operation sequenced on state thread @s@ to produce an @a@.
type Prim s a = State# s -> (# State# s, a #)

-- Unsafely run a @Prim@ operation on another state thread.
rethreadPrim :: Prim s a -> Prim t a
rethreadPrim primOp = \t -> case primOp (unsafeCoerceZeroBit t) of
  (# t', a #) -> (# unsafeCoerceZeroBit t', a #)
 where
  unsafeCoerceZeroBit :: forall (a :: ZeroBitType) (b :: ZeroBitType). a -> b
  unsafeCoerceZeroBit = unsafeCoerce#

-- Unsafely run a higher-order @Prim@ operation in @Cont@, re-scoping however necessary.
primitively :: (Prim s a -> Prim s b) -> Cont p a -> Cont q b
primitively hoPrimOp = fromPrim . hoPrimOp . toPrim

-- Unsafely run @Cont@ in any state thread.
toPrim :: Cont p a -> Prim s a
toPrim = rethreadPrim . unCont

-- Unsafely run @Prim@ in any scope.
fromPrim :: Prim s a -> Cont p a
fromPrim = Cont . rethreadPrim

-- }}}

-- --< Cont >-- {{{

-- | An t'ST'-like monad enriched with native delimited continuation operators.
--   Rather than a state thread, however, @Cont@ has a /scope/ parameter restricting control operators to the domain of their definition.
type Cont :: Scope -> Type -> Type
newtype Cont p a = Cont{ unCont :: Prim p a }
  deriving (Functor, Applicative, Monad, MonadFix)
    via ST p
  deriving (Semigroup, Monoid)
    via ST p a

{- |

Run t'Cont' purely, isolated in its own universe.

==== Reduction Semantics

\( \runCont \) extends \( L_\Hask \) with terms of the form \( \runCont \app e \).
The corresponding reduction axioms are twofold. \[
\begin{align*}
  \runCont \app (\pure \app h) &\redAx_\Hask h \\
  \runCont \app e &\redAx_\Hask \runCont \app e' \iff e \step e'
\end{align*}
\]

-}
runCont :: (forall u. Cont u a) -> a
runCont c = runST (coerce c)

{- |

Lower a computation into a subscope.

==== Reduction Semantics

\( \hslower\hash \) is a coercion; it's erased before execution and consequently has no role in the reduction semantics.

-}
lower# :: p ~~< q -> Cont q a -> Cont p a
lower# !_ = primitively id

{- |

Run t'Cont' 'RealWorld' in t'IO'.

==== Reduction Semantics

See 'ioToCont'.

-}
contToIO :: Cont RealWorld a -> IO a
contToIO = coerce

{- |

Run t'IO' in the 'RealWorld' scope.

==== Reduction Semantics

In implementation, \( \contToIO \) and \( \ioToCont \) are both coercions.
Morally, however, they extend \( L_\IO \) with terms of the form \( \contToIO \app e \).
The corresponding reduction axioms are threefold. \[
\begin{align*}
  \contToIO \app (\pure \app h)
    &\redAx_\IO \pure \app h \\
  \contToIO \app {\E} \sq{\ioToCont \app i}
    &\redAx_\IO i \bind \lam x { \contToIO \app {{\E} \sq{\pure \app x}} } \\
  \contToIO \app e
    &\redAx_\IO \contToIO \app e' \iff e \step e'
\end{align*}
\]

-}
ioToCont :: IO a -> Cont RealWorld a
ioToCont = coerce

{- |

The existence of 'Control.Monad.ST.Lazy.lazyToStrictST' is what makes this function unsafe.
Only __strict__ t'ST' actions may be safely run in t'Cont'.

==== Reduction Semantics

Coercion.

-}
unsafeSTToCont :: ST s a -> Cont s a
unsafeSTToCont = coerce

-- }}}

-- --< Limit# >-- {{{

-- | A @Limit# p q a@ delimits from @q@ a direct subscope @p@ in which an @a@ is to be computed.
type role Limit# nominal nominal representational
type Limit# :: Scope -> Scope -> Type -> UnliftedType
newtype Limit# p q a = Limit#{ tag :: PromptTag# a }

{- |

Create a new t'Limit#' and hence a new subscope @p@.

==== Reduction Semantics

Morally a /limit binder/ under which execution continues.
In \( L_\Cont \) we have \( \delta l. \, e \) to explicitly bind and lexically scope the limit \( l \) to the body \( e \), but in Haskell we can only emulate \( \delta \) with \( \newLimit\hash \lambda \) and wield rank-n types to prevent \( l \) from escaping its scope.

\[
  \newLimit\hash \app \lam l {\pure \app h}
    \redAx \pure \app h
\]

-}
newLimit# :: (forall p. Limit# p q a -> Cont q r) -> Cont q r
newLimit# k = fromPrim \rw -> case newPromptTag# rw of
  (# rw', tag #) -> toPrim (k Limit#{tag}) rw'

{- |

Impose a t'Limit#', encapsulating a computation within a direct subscope.

==== Reduction Semantics

Execution continues under the limit.

\[
  \impose\hash \app l \app {\left( \pure \app h \right)}
    \redAx \pure \app h
\]

-}
impose# :: forall p q a. Limit# p q a -> Cont p a -> Cont q a
impose# Limit#{tag} = primitively (prompt# tag)

-- | A @t'Limit#' p q a@ witnesses that \( p \sub q \).
evince# :: Limit# p q a -> p ~~< q
evince# !_ = UnsafeSubScopeProof# (# #)

-- | Compare t'Limit#'s, dynamically reclaiming any lost type-level information.
sameLimit#
  :: forall p q r s a b
   . Limit# p r a -> Limit# q s b
  -> Maybe (p :~: q, r :~: s, Coercion a b)
l1 `sameLimit#` l2 = testPromptTag# (tag l1) (tag l2) <&> \co ->
  ( unsafeCoerce (Refl :: p :~: p)
  , unsafeCoerce (Refl :: r :~: r)
  , co
  )
 where
  -- Check two 'PromptTag#'s for pointer equality, producing a proof of representational equality upon success.
  -- See: https://gitlab.haskell.org/ghc/ghc/-/issues/24994
  testPromptTag# :: PromptTag# a -> PromptTag# b -> Maybe (Coercion a b)
  testPromptTag# pta ptb
    | isTrue# (unsafePtrEquality# pta ptb) = Just (unsafeCoerce refl_)
    | otherwise                            = Nothing
   where
    refl_ = Coercion @a @a

-- }}}

-- --< sunder# >-- {{{

{-|

Sunder the continuation at the t'Limit#', destroying it before capturing the liberated portion of the continuation.

==== Relatives

 - \( \F - - \)
 - withSubCont
 - cupto
 - control0

==== Reduction Semantics

The sole control operator, defined only when executed under the corresponding limit. \[
  \impose\hash \app l
    \app {\E_x} \sq{\sunder\hash \app p \app l \app h}
      \redAx h \app \lam y {{\E_x} \sq y}
\]
This pseudo-axiom is /simplified/; it treats \( L_\Hask \) as a macro language over \( L_\Cont \), implicitly reducing an \( h \) to a corresponding \( e \) term.
Strictly speaking, however, the RHS must be in \( L_\Cont \) or the reduction axiom is ill formed.
The true axiom is \[
  \impose\hash \app l
    \app {\E_x} \sq{\sunder\hash \app p \app l \app h}
      \redAx {\proj} \br{
        {\eval_\Hask} \br{h \app \lam y {{\E_x} \sq y}}
      }
\] where \[
\begin{align*}
  &\eval_\Hask(\cdot) : L_\Hask \parto L_\Hask^v \\
  &\eval_\Hask(h) = v_h \iff h \step_\Hask^* v_h \\
  &{\proj} \br \cdot : L_\Hask \parto L_\text{Cont} \\
  &{\proj} \br h = e \iff h = e,
\end{align*}
\] restricted to cases for which both partial functions are defined.

/Reductions for derivative control operators will henceforth be given in simplified, pseudo-axiom form./

-}
sunder#
  :: p ~~< q -> Limit# q r a {- ^ -}
  -> ((Cont p b -> Cont q a) -> Cont r a) -> Cont p b
sunder# !_ Limit#{tag} withk
  = fromPrim $ GHC.control0# tag (toPrim . withk . primitively)

-- }}}

-- --< About >-- {{{

-- --< Safety >-- {{{

{- $Safety
/Safety/ is context-dependent.
This section details the precise notion of safety used in this library—any observable violation is considered a /bug/ and should be reported as such.
-}

-- --< Purity >-- {{{

{- $Purity

Purity is a property of Haskell; it goes without saying that a Haskell library should expose a pure interface.
This library guards its effects behind t'Cont' actions, which can be executed in two ways.
The first, 'contToIO', does so in an t'IO' context—it can be presumed pure.
The second, 'runCont', requires some justification.

A hand-waving argument is that @t'Cont' s a@ can be modelled within @'Control.Monad.Trans.Cont.ContT' a ('ST' s) a@, for which @run@ is pure.

@
run :: (forall s. 'Control.Monad.Trans.Cont.ContT' a ('ST' s) a) -> a
run act = 'runST' ('Control.Monad.Trans.Cont.runContT' act 'pure')
@

A rigourous proof can likely be obtained by extending the rather tedious work done for 'runST'.

-}

-- }}}

-- --< Well-Scopedness >-- {{{

{- $Well-Scopedness

A /delimited/ control operator is only well-defined within the scope of a matching delimiter.
The core interface is hence carefully crafted to ensure well-scopedness:

  1. The scope of a computation is represented at the type level, parameterising t'Cont'.

  2. When a new delimiter tag—a t'Limit#'—is created, it records both the scope it was created in and a newly created direct subscope:

       @'newLimit#' :: (forall q. t'Limit#' q r a -> t'Cont' r b) -> t'Cont' r b@

  3. Delimitation of scopes is mandatory; the only way to run @t'Cont' q a@ is to 'impose#' the @t'Limit#' q r a@ in @r@, thereby delimiting @q@ from @r@:

       @'impose#' :: t'Limit#' q r a -> t'Cont' q a -> t'Cont' r a@

  4. @s@ is a /direct/ subscope of @t@ iff \( \exists \! \) @x@ \( \exists \! \) @l :: t'Limit#' s t x@.
     To also account for /indirect/ subscopes, we use

       @'evince#' :: t'Limit#' s t x -> s t'NativeCont.~~<' t@

       to extract proof tokens exhibiting transitivity via composition.

       @'(~)' :: t t'NativeCont.~~<' u -> s t'NativeCont.~~<' t -> s t'NativeCont.~~<' u@

  5. Finally, our control operator 'sunder#' requires a proof that the scope @p@ it's invoked from is a subscope of @q@:

       @
       'sunder#'
         :: p t'NativeCont.~~<' q
         -> t'Limit#' q r a
         -> (('Cont' p b -> t'Cont' q a) -> t'Cont' r a)
         -> t'Cont' p b
       @

       Note also the precise typing of the function argument—we abort up to and /including/ what delimits @q@ from @r@, so the working scope must then become @r@.
       The continuation, on the other hand, is captured up to but /not including/ the delimiter, so it must be reified at @t'Cont' p b -> t'Cont' q a@.
       As such, the @t'Limit#' q r a@ must be reinstated before the supplied continuation can be used.
       @sever@ and @control@ are simply the two extremal choices for its reinstatement, while @shift@—rendered insensible by a dramatic improvement in typing discipline—is both choices at the same time.

-}

-- }}}

-- --< Threading Invariants >-- {{{

{- $Threading_Invariants

The implementation of the native delimited continuation primops requires some
/threading invariants/ for safe usage.
In particular:

  * They must run on a /strict/ state thread.

      We ensure this by definition of t'Cont' and by interoperating only with t'IO' and (strict) t'ST'.

  * There must be no breaks in the state thread linking @'impose#' l@ and @'sunder#' p l@; i.e. the delimited continuation must include no intervening uses of 'System.IO.Unsafe.unsafePerformIO', 'runST', 'System.IO.Unsafe.unsafeInterleaveIO', 'runCont', etc.

      We obtain this en route to well-scopedness: the proof @p@ that one may @'sunder#' p l@ doubles as proof of an unbroken thread to @'impose#' l@.

  * The state thread in question must not belong to an 'Control.Monad.STM.STM' transaction.

      We provide no @runContSTM@, and prohibitions against t'IO' prevent 'contToIO' from posing a problem.
      'runCont' introduces its own state thread.

-}

-- }}}

-- --< IO Interface Preservation >-- {{{

{- $IO_Interface_Preservation

The t'IO' operations found in the wild are at best written to be safe with respect to the t'IO' interface of their time.
Rashly extending t'IO' directly with continuation manipulation operations would break that safety.
Taking the widely used 'Control.Exception.bracket' as an example, an abort would escape the main body without ever running the all-important clean-up, while multiple re-entrance would instead attempt to reuse a resource that's no longer available.

Regardless, we need some way to use continuation operations within and around t'IO' operations or too much expressivity is lost.
'contToIO' and 'ioToCont' are designed to mediate this tension, and we claim they don't break pre-existing t'IO' operations: while 'contToIO' allows us to embed t'Cont' in t'IO', control operators used within can only manipulate the continuation /beneath/ its invocation.

-}

-- }}}

-- }}}

-- --< This Documentation >-- {{{

-- --< Derivations >-- {{{

{- $Derivations

The core interface that "NativeCont" exposes is minimal in a precise sense: as a set of /atoms/ it has no redundant elements.

The other modules are not so: their offerings are /derived/ from the atoms.
The reduction of such an entity to its core building blocks is a form of semantics—the entity may be understood in terms of its components.
As such, whenever non-trivial, /derivations/ are given in documentation—not directly from the core interface, but always from something /strictly simpler/.
This keeps the derivations themselves as simple as possible, while clarifying the relationships between derived entities.

N.B. \( \declare{X} \declare{foo} \declare{auto} \)

  - Though @<|@, @auto@ and @reflect@ are not strictly fundamental, they /are/ atoms of "Control.Continuation.Inferred".

  - Elided trivial derivations include:

      - The derivation of @foo@ directly from @foo#@.
        These functions only unwrap data to pass the unlifted innards down to @foo#@.

      - The multitude of cases in "Control.Continuation.Inferred" where \( \foo := \X\qual\foo \app \auto \).

      - Aliases.

-}

-- }}}

-- --< Reduction Semantics >-- {{{

{- $Reduction_Semantics

Recommended watching: [Basic Mechanics of Operational Semantics](https://www.youtube.com/watch?v=exhwykjH_z4) by David Van Horn (39:09).

Recommended reading: [Continuations and Reduction Semantics](https://gist.github.com/lexi-lambda/d97b8187a9b63619af29689e9fa1b880) by Alexis King.

Notation and terminology vary between authors, so we clarify our own conventions here while offering some basic explanation.

==== Metavariables

Basic:

 * \( x, y \): distinct \( \lambda \)-bound variables.
 * \( l \): limits.
 * \( p \): proof tokens.

Languages: \[
\begin{alignat*}{3}
  &L_\Hask \quad\quad &&h   &&::=
    v_h \| h_1 \app h_2 \| \runCont \app e \| \ldots \\
  &L_\Hask^v          &&v_h &&::=
    \lam x h \| e \| i \| \ldots \\
  &L_\Cont &&e   &&::=
    v_e \| e \bind h \| \del l e \| \impose \app l \app e
        \| \sunder \app l \app h \| \ioToCont \app i \| \ldots \\
  &L_\Cont^v          &&v_e &&::=
    x \| \pure \app h \\
  &L_\IO              &&i   &&::=
    v_i \| i \bind h \| \contToIO \app e \| \ldots \\
  &L_\IO^v            &&v_i &&::=
    x \| \pure \app h
\end{alignat*}
\]

N.B.

  * Reductions given in identifier documentation use full Haskell identifiers and arguments, e.g. \( \sunder\hash \app p \app l \app h \) rather than \( \sunder \app l \app h \) as above.

  * To avoid visual confusion with the \( \redAx \) relation, we elect to notate all our binders with \( . \) rather than \( \to \).

Execution context for \( L_\Cont \): \[
  \E_x ::= \hole
         \| \E_x \bind h
         \| \del l \E_x
         \| \impose \app y \app {\E_x}
\]

==== Reduction Axiomata & Relations

Reduction axiom /schemata/ (more precisely) are the rules that determine how the syntactic elements of a language reduce.
We denote these rules with \( \redAx \), choosing them carefully such that the resulting \( \redAx \) relation is /functional/ and does not relate /values/. \[
\begin{gather*}
  e \redAx e_a \wedge e \redAx e_b \implies e_a = e_b \\
  v_e \Not\redAx e
\end{gather*}
\]

An evaluation (or execution) context is a special one-hole context for a language imposing a unique order upon the evaluation of sub-expressions.
An associated hole-filling operation \( {\E} \sq{\cdot} : L \to L \) allows us to conveniently factor a /redex/ \( e_1 = {\E} \sq{e_2} \) into a /continuation/ \( \E \) and a smaller redex \( e_2 \), so we can easily manipulate the former when it's relevant or ignore it when it isn't.
In particular, an evaluation context lets us construct the one-step relation \( \step \) from \( \redAx \) such that it can be seen to inherit the key properties of the latter. \[
  {\E} \sq e \step {\E} \sq{e'} \iff e \redAx e'
\]

The reflexive-transitive closure \( \step^* \) then allows us to fully define evaluation, as we do in 'sunder#' for \( L_\Hask \). \[
\begin{align*}
  &\eval(\cdot) : L \parto L^v \\
  &\eval(e) = v_e \iff e \step^* v_e
\end{align*}
\]

-}

-- }}}

-- }}}

-- }}}

