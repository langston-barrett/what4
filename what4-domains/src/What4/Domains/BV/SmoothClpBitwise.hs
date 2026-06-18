{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : What4.Domains.BV.SmoothClpBitwise
Copyright   : (c) Galois Inc, 2026
License     : BSD3

The reduced product of 'What4.Domains.BV.SmoothClp' and
'What4.Domains.BV.Bitwise'. Pairs a SmoothClp component with a bitwise
component and applies 'S.reduce' after every operation, so callers see
the joint information of both views without having to manage the pair
themselves.
-}
module What4.Domains.BV.SmoothClpBitwise
  ( Domain
  , strides
  , bitwise
  , proper
  -- * Construction
  , mk
  , top
  , fromAscEltList
  -- * Canonicalization
  , Canonical
  , getCanonical
  , canonicalize
  -- * Conversion
  , toArith
  , hull
  , fromArith
  , toBitwise
  , forcedBits
  , fromBitwise
  -- * Queries
  , member
  , toList
  , size
  , leq
  , leqPrecise
  , isSelfWrapping
  -- * Arithmetic
  , negate
  , add
  , sub
  , scale
  , mul
  , mulPrecise
  , udiv
  , udivPrecise
  , urem
  , uremPrecise
  , sdiv
  , srem
  -- ** Arithmetic (SMT-LIB div-by-zero semantics)
  , udivSmtlib
  , uremSmtlib
  , sdivSmtlib
  , sremSmtlib
  -- ** Arithmetic (LLVM overflow flags)
  , addNuw
  , addNsw
  , addNswNuw
  , subNuw
  , subNsw
  , subNswNuw
  , mulNuw
  , mulNsw
  , mulNswNuw
  , shlNuw
  , shlNsw
  , shlNswNuw
  , udivExact
  , sdivExact
  , lshrExact
  , ashrExact
  -- * Bitwise operations
  , not
  , andFast
  , and
  , andPrecise
  , orFast
  , or
  , orPrecise
  , xorFast
  , xor
  -- * Concatenation, extension, selection, and truncation
  , zext
  , sext
  , concat
  , select
  -- * Shifts and rotations
  , shl
  , shlRaw
  , lshr
  , lshrRaw
  , ashr
  , ashrRaw
  , rol
  , rolRaw
  , ror
  , rorRaw
  -- * Lattice operations
  -- ** Meets
  , pseudoMeet
  , pseudoMeetPrecise
  -- ** Joins
  , pseudoJoin
  , pseudoJoinPrecise
  -- * Branch-condition assumptions
  , assumeUlt
  , assumeUle
  , assumeUgt
  , assumeUge
  , assumeSlt
  , assumeSltPrecise
  , assumeSle
  , assumeSlePrecise
  , assumeSgt
  , assumeSgtPrecise
  , assumeSge
  , assumeSgePrecise
  , assumeEq
  , assumeNe
  -- * Generators
  , genDomain
  , genElement
  , genPair
  -- * Properties
  -- ** Construction
  , fromAscEltListMember
  -- ** Canonicalization
  , canonLossless
  , canonProper
  , canonIdempotent
  -- ** Conversion
  , toArithCorrect
  , fromArithCorrect
  , roundtripArith
  , toBitwiseCorrect
  , forcedBitsMember
  , fromBitwiseCorrect
  -- ** Queries
  , toListMember
  , memberToList
  , toListNoDuplicates
  , leqCorrect
  , leqReflexive
  , leqTransitive
  , leqPreciseCorrect
  , leqPreciseReflexive
  , sizeViaToList
  , sizeAtMostComponents
  , sizeExactCorrect
  , windowMarginalCount
  , uniformWindowBalanced
  , pinsConflictEmpty
  -- ** Arithmetic
  , correct_neg
  , correct_add
  , correct_sub
  , correct_scale
  , correct_mul
  , correct_mulPrecise
  , correct_udiv
  , correct_udivPrecise
  , correct_urem
  , correct_uremPrecise
  , correct_sdiv
  , correct_srem
  -- *** Exactness
  , addExact
  , subExact
  -- mulConstExact removed under smoothing (see SmoothClp.hs)
  , udivConstExact
  , uremConstExact
  , ultExactTrueSeparated
  , ultExactFalseSeparated
  -- *** Arithmetic (SMT-LIB div-by-zero semantics)
  , correct_udivSmtlib
  , correct_uremSmtlib
  , correct_sdivSmtlib
  , correct_sremSmtlib
  -- *** Arithmetic (LLVM overflow flags)
  , correct_addNuw
  , correct_addNsw
  , correct_addNswNuw
  , correct_subNuw
  , correct_subNsw
  , correct_subNswNuw
  , correct_mulNuw
  , correct_mulNsw
  , correct_mulNswNuw
  , correct_shlNuw
  , correct_shlNsw
  , correct_shlNswNuw
  , correct_udivExact
  , correct_sdivExact
  , correct_lshrExact
  , correct_ashrExact
  -- ** Bitwise operations
  , correct_not
  , correct_and
  , correct_or
  , correct_xor
  , correct_andPrecise
  , correct_orPrecise
  -- ** Concatenation, extension, selection, and truncation
  , correct_zero_ext
  , correct_sign_ext
  , correct_concat
  , correct_select
  -- ** Shifts and rotations
  , correct_shl
  , correct_lshr
  , correct_ashr
  , correct_rol
  , correct_ror
  -- ** Lattice operations
  -- *** Meets
  , correct_pseudoMeet
  , correct_pseudoMeetPrecise
  , pseudoMeetLowerBound
  , pseudoMeetPreciseLowerBound
  , pseudoMeetCommutative
  , pseudoMeetPreciseCommutative
  , pseudoMeetIdempotent
  , pseudoMeetPreciseIdempotent
  , pseudoMeetTopIdentity
  , pseudoMeetPreciseTopIdentity
  -- *** Joins
  , correct_pseudoJoin
  , correct_pseudoJoinPrecise
  , pseudoJoinUpperBound
  , pseudoJoinPreciseUpperBound
  , pseudoJoinCommutative
  , pseudoJoinPreciseCommutative
  , pseudoJoinIdempotent
  , pseudoJoinPreciseIdempotent
  , pseudoJoinPreciseRefinesJoin
  , pseudoJoinTopAnnihilator
  , pseudoJoinPreciseTopAnnihilator
  -- ** Branch-condition assumptions
  , correct_assumeUlt
  , correct_assumeUle
  , correct_assumeUgt
  , correct_assumeUge
  , correct_assumeSlt
  , correct_assumeSle
  , correct_assumeSgt
  , correct_assumeSge
  , correct_assumeSltPrecise
  , correct_assumeSlePrecise
  , correct_assumeSgtPrecise
  , correct_assumeSgePrecise
  , correct_assumeEq
  , correct_assumeNe
  , assumeUltShrinks
  , assumeUleShrinks
  , assumeUgtShrinks
  , assumeUgeShrinks
  , assumeSltShrinks
  , assumeSleShrinks
  , assumeSgtShrinks
  , assumeSgeShrinks
  , assumeSltPreciseShrinks
  , assumeSlePreciseShrinks
  , assumeSgtPreciseShrinks
  , assumeSgePreciseShrinks
  , assumeNeShrinks
  , assumeSltPreciseIdempotent
  , assumeSlePreciseIdempotent
  , assumeSgtPreciseIdempotent
  , assumeSgePreciseIdempotent
    -- * Re-exports
  , NatRepr
  , knownNat
  ) where

import           GHC.TypeNats (Nat, type (+), type (<=))
import           Numeric.Natural (Natural)
import           Prelude hiding (negate, not, and, or, concat)
import qualified Prelude

import qualified Data.Bits as Bits
import qualified Data.List as List
import qualified Data.Set as Set

import           Data.Parameterized.NatRepr (NatRepr, LeqProof(..), knownNat)
import qualified Data.Parameterized.NatRepr as NR

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import           What4.Domains.BV.Bounds (UnsignedBounds(..))
import qualified What4.Domains.BV.SmoothClp as S
import           What4.Domains.Verification (Property, property, (==>), Gen)

-- ------------------------------------------------------------------
-- The reduced-product domain

-- | A reduced product of 'S.Domain' and 'B.Domain'. Each component is
-- always reduced with respect to the other (no bit forced by the
-- bitwise component contradicts the strides orbit, no orbit element
-- violates a forced bit). Construct with 'mk', 'top', or any of the
-- lifted operations.
data Domain (w :: Nat)
  = Domain
    { strides :: !(S.Domain w)
    , bitwise :: !(B.Domain w)
    }
  deriving Show

-- | The data-structure invariants of 'Domain': both components are
-- 'proper' and at the same width.
proper :: Domain w -> Bool
proper (Domain s b) =
  S.proper s && toInteger (S.mask s) == B.bvdMask b

-- | Smart constructor: build a 'Domain' from a strides+bitwise pair by
-- running 'S.reduce'. If 'S.reduce' returns 'Nothing' (it concluded the
-- joint is empty), fall back to dropping the bitwise component:
-- @'mkReduced' w s ('S.toBitwise' s)@. The fallback is sound (the
-- strides component on its own is a non-empty over-approximation),
-- though it loses whatever information @b@ carried. 'S.reduce' is not
-- complete on every (s, b) pair (e.g. on self-wrapping orbits whose
-- arc clip is conservatively skipped), so callers can\'t rely on
-- 'Nothing' implying an actually-empty joint. Use 'tryMkReduced' when
-- the operation should propagate \"empty joint\" rather than fall back.
mkReduced :: (1 <= w) => NatRepr w -> S.Domain w -> B.Domain w -> Domain w
mkReduced = mkReducedBy S.reduce

-- | Like 'mkReduced', but uses 'S.reducePrecise' (the precise mutual
-- refinement, per-piece stride lift + numeric-arc clip). This is where the
-- bitwise component's known bits are lifted into the strides orbit (and the
-- tightened orbit\'s bits pushed back into the bitwise component) more
-- aggressively than single-pass 'S.reduce'. Used by the @*Precise@ operations.
--
-- 'S.reducePrecise' is sound but /incomplete/: on some self-wrapping orbits it
-- conservatively returns 'Nothing' (skipping the arc clip) even when the joint
-- is nonempty. So on 'Nothing' we do not conclude \"empty\"; we fall back to
-- single-pass 'mkReduced', which handles those cases (and the genuine
-- empty-joint fallback). This never loses precision relative to 'mkReduced'.
mkReducedPrecise :: (1 <= w) => NatRepr w -> S.Domain w -> B.Domain w -> Domain w
mkReducedPrecise w s b = case S.reducePrecise w s b of
  Just (s', b') -> Domain s' b'
  Nothing       -> mkReduced w s b

-- | Shared driver for 'mkReduced' / 'mkReducedPrecise', parameterized over the
-- reduction. On a 'Nothing' (joint concluded empty) it falls back to dropping
-- the bitwise component (@reduceOp w s (S.toBitwise s)@); see 'mkReduced'.
mkReducedBy ::
  (1 <= w) =>
  (NatRepr w -> S.Domain w -> B.Domain w -> Maybe (S.Domain w, B.Domain w)) ->
  NatRepr w -> S.Domain w -> B.Domain w -> Domain w
mkReducedBy reduceOp w s b = case reduceOp w s b of
  Just (s', b') -> Domain s' b'
  Nothing ->
    case reduceOp w s (S.toBitwise s) of
      Just (s', b') -> Domain s' b'
      Nothing       -> error "SmoothClpBitwise.mkReducedBy: reduce failed on \
                             \(s, toBitwise s) — invariant violated."

-- | Smart constructor for pairs whose strides component needs no refinement
-- from the bitwise side (only the reverse). Builds the same reduced product as
-- 'mkReduced' on such pairs, and is sound on any pair. Restricted to callers
-- that guarantee this: 'add'\/'sub' and the feed-forward 'fromArith'.
mkReducedProject :: (1 <= w) => NatRepr w -> S.Domain w -> B.Domain w -> Domain w
-- Runs the projection-only 'S.reduceProject' in place of the full 'S.reduce'.
-- The precision-regression CSV is byte-identical to the 'mkReduced' baseline,
-- confirming the restriction holds across the corpus.
mkReducedProject = mkReducedBy S.reduceProject

-- | Build a 'Domain' from a pair that is already mutually reduced, doing no
-- reduction work. The caller must guarantee the reduced-product invariant: no
-- bit forced by the bitwise component contradicts the orbit, and the orbit's
-- lowest stride bit matches the bitwise component's lowest free bit.
fromConsistent :: S.Domain w -> B.Domain w -> Domain w
-- The one safe caller is 'fromBitwise', which builds the orbit @s@ from @b@'s
-- forced bits: @b@ is then already a subset of @s@'s projection, so the full
-- 'S.reduce' would return @(s, b)@ unchanged.
fromConsistent = Domain

-- | Strict smart constructor: returns 'Nothing' iff the reduction concludes
-- the joint is empty. Use this from @Maybe Domain@-returning operations
-- (e.g. 'pseudoMeet', 'lowerBound') so that an empty joint propagates
-- as 'Nothing' rather than silently widening to 'mkReduced'\'s fallback,
-- which would drop @b@ and admit values not in either operand.
tryMkReduced ::
  (1 <= w) => NatRepr w -> S.Domain w -> B.Domain w -> Maybe (Domain w)
tryMkReduced w s b = case S.reduce w s b of
  Just (s', b') -> Just (Domain s' b')
  Nothing       -> Nothing

-- | Like 'tryMkReduced', but uses 'S.reducePrecise' (see 'mkReducedPrecise').
-- Because 'S.reducePrecise' is incomplete on self-wrapping orbits (it can
-- return 'Nothing' on a nonempty joint), a 'Nothing' here does /not/ mean
-- empty: we defer to single-pass 'tryMkReduced', which only reports 'Nothing'
-- when the joint genuinely is empty.
tryMkReducedPrecise ::
  (1 <= w) => NatRepr w -> S.Domain w -> B.Domain w -> Maybe (Domain w)
tryMkReducedPrecise w s b = case S.reducePrecise w s b of
  Just (s', b') -> Just (Domain s' b')
  Nothing       -> tryMkReduced w s b

-- ------------------------------------------------------------------
-- * Construction

-- | Build a reduced product directly from a (start, stride, n).
mk ::
  (1 <= w) =>
  NatRepr w -> Natural -> Natural -> Natural -> Domain w
mk w s t nn =
  let sd = S.mk w s t nn
  in mkReduced w sd (S.toBitwise sd)

-- | The top element: every bitvector at width @w@.
top :: (1 <= w) => NatRepr w -> Domain w
top w = mkReduced w (S.top w) (B.top w)

-- | Build from a strictly-ascending element list. 'Nothing' on the
-- empty list (which would denote an empty set).
fromAscEltList ::
  (1 <= w) => NatRepr w -> [Natural] -> Maybe (Domain w)
fromAscEltList w xs =
  case S.fromAscEltList w xs of
    Nothing -> Nothing
    Just sd -> Just (mkReduced w sd (S.toBitwise sd))

-- ------------------------------------------------------------------
-- * Canonicalization

-- | Lossless canonical form of a 'Domain'. Two reduced products denote
-- the same set iff their 'canonicalize' results are equal.
newtype Canonical w = Canonical (Domain w)
  deriving Show

-- | The underlying canonical 'Domain'.
getCanonical :: Canonical w -> Domain w
getCanonical (Canonical c) = c

-- | Canonicalize the strides component; the bitwise component is left
-- as-is (it's already exactly determined by the strides component
-- after reduction, modulo orientation).
canonicalize :: Domain w -> Canonical w
canonicalize (Domain s b) =
  Canonical (Domain (S.getCanonical (S.canonicalize s)) b)

-- ------------------------------------------------------------------
-- * Conversion

-- | Project to an arithmetic-interval domain via the strides component.
toArith :: Domain w -> A.Domain w
toArith (Domain s _) = S.toArith s

-- | The arithmetic hull of the strides component (the arc
-- @[start, start + n*stride]@).
hull :: Domain w -> A.Domain w
hull (Domain s _) = S.hull s

-- | Refine an arithmetic-domain element into the reduced product.
-- 'Nothing' if 'S.fromArith' returns 'Nothing'.
fromArith ::
  (1 <= w) => NatRepr w -> A.Domain w -> Maybe (Domain w)
fromArith w a = case S.fromArith w a of
  Nothing -> Nothing
  -- Feed-forward: pair the orbit with its own projection. The lift is a no-op
  -- (the projection leaves bit @ctz(stride)@ free), so the projection-only
  -- reduce suffices and equals the full 'mkReduced'.
  Just sd -> Just (mkReducedProject w sd (S.toBitwise sd))

-- | Project to the bitwise component.
toBitwise :: Domain w -> B.Domain w
toBitwise (Domain _ b) = b

-- | The forced @(zeros, ones)@ pair of the strides component.
forcedBits :: Domain w -> (Natural, Natural)
forcedBits (Domain s _) = S.forcedBits s

-- | Refine a bitwise-domain element into the reduced product.
-- 'Nothing' if 'S.fromBitwise' returns 'Nothing'.
fromBitwise ::
  (1 <= w) => NatRepr w -> B.Domain w -> Maybe (Domain w)
fromBitwise w b = case S.fromBitwise w b of
  Nothing -> Nothing
  -- Feed-forward: @sd@ is built from @b@\'s forced bits, so @b@ is already a
  -- subset of @sd@\'s projection and the full reduce returns @(sd, b)@ unchanged.
  -- Settle the pair directly, with no reduction work.
  Just sd -> Just (fromConsistent sd b)

-- ------------------------------------------------------------------
-- * Queries

-- | Membership: a value is in the reduced product iff it is in /both/
-- components. After reduction, the bitwise check is redundant (every
-- orbit element already satisfies the bitwise constraint), but we
-- check both anyway as a defensive sanity check.
member :: Domain w -> Natural -> Bool
member (Domain s b) x = S.member s x && B.member b (toInteger x)

-- | Enumerate the joint set: orbit elements that also satisfy the
-- bitwise component. The reduction invariant tightens both components
-- but does not in general guarantee that every orbit element passes
-- the bitwise check, so we filter.
toList :: Domain w -> [Natural]
toList (Domain s b) =
  [ x | x <- S.toList s, B.member b (toInteger x) ]

-- | Cardinality of the joint set: orbit elements that also satisfy the
-- bitwise component, bounded above by both 'S.size' of the strides
-- component and 'B.size' of the bitwise component. Always /O(M(w))/ (from
-- 'S.forcedBits').
--
-- __Exactness via the orbit's uniform window.__ Write @2^k =
-- gcd(stride, 2^w)@ and @2^s@ for the largest power of two dividing the
-- orbit length @n+1@. Then across the orbit:
--
--   * bits @[0, k)@ are /constant/ (every element shares @start@\'s low
--     bits), and
--   * bits @[k, k+s)@ are /uniform/: each of the @2^s@ combinations occurs
--     in exactly @(n+1)\/2^s@ elements, jointly and independently.
--
-- (Bits @[0,k)@ are pinned by the stride; bits @[k,k+s)@ cycle with full
-- period because @stride\/2^k@ is odd, and @2^s | n+1@ makes the cycle
-- divide the orbit evenly.)
--
-- A /cut bit/ is a position that @b@ pins (forces to 0 or 1) but @s@
-- leaves varying across the orbit. The name is what it does to the count:
-- it is exactly the bits where @b@\'s constraint actually removes orbit
-- elements. A bit @b@ pins that @s@ /also/ pins adds no constraint (every
-- orbit element already agrees, or none does (a conflict, see below); a
-- bit @b@ leaves free constrains nothing. So only the cut bits thin the
-- orbit, and over a uniform window each one independently keeps half the
-- elements.
--
-- Hence if every cut bit lies in the uniform window @[k, k+s)@, the answer
-- is __exact__: @(n+1) \/ 2^(number of cut bits)@. This subsumes both the
-- /entailment/ case (no cut bits ⇒ @'S.size' s@) and the /full coset/ case
-- (@s = w-k@, the window is every high bit), and additionally nails many
-- partial orbits. A forced bit conflicting with one @s@ pins makes the
-- joint empty (@0@).
--
-- Otherwise, when a cut bit lies above the uniform window (where the orbit
-- shears across bit positions), the exact count @|AP ∩ bit-cube|@ has no
-- closed form and is exponential in @w@. Rather than enumerate the orbit we
-- return a sound /over-approximation/: the minimum of @'S.size' s@,
-- @'B.size' b@, @2^(bits free in both components)@, and the /window
-- marginal/ 'windowMarginal'. The last still exploits the orbit's balance:
-- the in-window cut bits each exactly halve the count, so
-- @(n+1)\/2^(in-window cut bits)@ is the exact number of orbit elements
-- matching the in-window forced bits, hence an upper bound on the joint set
-- (which additionally honors the above-window bits). This is typically far
-- tighter than the @2^(bits free in both)@ ceiling.
size :: Domain w -> Natural
size c@(Domain s b) = case sizeExactMaybe c of
  Just k  -> k
  Nothing -> minimum [S.size s, fromInteger (B.size b), jointBound, windowMarginal c]
  where
    m          = B.bvdMask b
    (loB, hiB) = B.bitbounds b
    unknownB   = loB `Bits.xor` hiB
    (zerosS0, onesS0) = S.forcedBits s
    unknownS   = m `Bits.xor` (toInteger zerosS0 Bits..|. toInteger onesS0)
    -- Over-approximation for the non-uniform case: every joint element is
    -- pinned on every bit either component forces, so only bits free in
    -- both can vary.
    jointBound = Bits.bit (Bits.popCount (unknownS Bits..&. unknownB))

-- | /O(M(w))/. The exact joint cardinality when the orbit's structure pins it
-- down, or 'Nothing' when only an over-approximation is available. Exact in
-- two cases: @s@ and @b@ pin a bit to opposite values ('pinsConflict' ⇒ the
-- joint is empty), or every bit @b@ forces that @s@ leaves varying (a /cut/
-- bit) lies within @s@'s 'uniformWindowMask', each such bit independently
-- halves the uniformly-distributed count, giving @(n+1) \/ 2^(cut bits)@.
-- That second case is exactly when the 'windowMarginal' (which always counts
-- elements matching the in-window forced bits) honors /every/ forced bit, so
-- the marginal is the true count. See 'sizeExactCorrect'.
sizeExactMaybe :: Domain w -> Maybe Natural
sizeExactMaybe c@(Domain s b)
  | pinsConflict s b = Just 0
  | cutting Bits..&. Bits.complement window == 0 = Just (windowMarginal c)
  | otherwise = Nothing
  where
    m          = B.bvdMask b
    (loB, hiB) = B.bitbounds b
    unknownB   = loB `Bits.xor` hiB
    forcedB    = m `Bits.xor` unknownB                 -- bits @b@ pins
    (zerosS0, onesS0) = S.forcedBits s
    unknownS   = m `Bits.xor` (toInteger zerosS0 Bits..|. toInteger onesS0)
    cutting    = forcedB Bits..&. unknownS             -- @b@ pins, @s@ varies
    window     = toInteger (uniformWindowMask s)

-- | /O(M(w))/. The exact number of orbit elements (of the strides component)
-- that satisfy the bitwise component's forced bits __that lie in the uniform
-- window__ @[0, k+s)@, ignoring any forced bits above it. Because the orbit
-- is balanced over the window, each in-window /cut/ bit (one @b@ forces and
-- @s@ leaves varying) independently halves the count, giving
-- @(n+1) \/ 2^(in-window cut bits)@. This counts a superset of the joint set
-- (the joint set additionally honors the above-window forced bits), so it is
-- a sound upper bound on 'size', and it is /exact/ when no cut bit lies above
-- the window. See 'windowMarginalCount'.
windowMarginal :: Domain w -> Natural
windowMarginal (Domain s b) = (S.n s + 1) `Bits.shiftR` Bits.popCount cutWindow
  where
    m          = B.bvdMask b
    (loB, hiB) = B.bitbounds b
    unknownB   = loB `Bits.xor` hiB
    forcedB    = m `Bits.xor` unknownB
    (zerosS0, onesS0) = S.forcedBits s
    unknownS   = m `Bits.xor` (toInteger zerosS0 Bits..|. toInteger onesS0)
    cutWindow  = forcedB Bits..&. unknownS Bits..&. toInteger (uniformWindowMask s)

-- | /O(A(w))/. The low-bit mask of positions @[0, k+s)@ over which the strides
-- orbit is balanced: @2^k = gcd(stride, 2^w)@ pins bits @[0, k)@ constant,
-- and @2^s@ (the largest power of two dividing the orbit length @n+1@)
-- makes bits @[k, k+s)@ take every combination equally often. See
-- 'uniformWindowBalanced'.
uniformWindowMask :: S.Domain w -> Natural
uniformWindowMask s = g * lb - 1
  where
    st  = S.stride s
    g   = st `Bits.xor` (st Bits..&. (st - 1))   -- @2^k@
    lb  = np1 `Bits.xor` (np1 Bits..&. S.n s)    -- @2^s@
    np1 = S.n s + 1

-- | /O(M(w))/. Whether @s@ and @b@ pin some bit to opposite values, in which
-- case the joint set is empty (see 'pinsConflictEmpty'). Sound but not
-- complete: 'False' does not imply a nonempty joint, since 'S.forcedBits'
-- under-approximates @s@'s constant bits.
pinsConflict :: S.Domain w -> B.Domain w -> Bool
pinsConflict s b =
  loB Bits..&. zerosS /= 0 || zerosB Bits..&. onesS /= 0
  where
    m          = B.bvdMask b
    (loB, hiB) = B.bitbounds b
    zerosB     = m `Bits.xor` hiB
    (zerosS0, onesS0) = S.forcedBits s
    zerosS     = toInteger zerosS0
    onesS      = toInteger onesS0

-- | Lattice ordering (cheap approximation): conjunction of per-component
-- 'leq's. Both must hold because the strides component does not in general
-- absorb the bitwise component's forced bits.
leq :: Domain w -> Domain w -> Bool
leq a b = S.leq (strides a) (strides b) && B.leq (bitwise a) (bitwise b)

-- | More precise ordering.
leqPrecise :: Domain w -> Domain w -> Bool
leqPrecise a b = S.leqPrecise (strides a) (strides b) && B.leq (bitwise a) (bitwise b)

-- | Whether the strides component is self-wrapping.
isSelfWrapping :: Domain w -> Bool
isSelfWrapping (Domain s _) = S.isSelfWrapping s

-- ------------------------------------------------------------------
-- * Internal helpers

-- | /O(M(w))/. The tightest sound unsigned value range for an operand: the
-- strides component's arithmetic bounds ('S.toArith' then 'A.ubounds')
-- intersected with the bitwise component's bit-pattern bounds ('B.bitbounds').
-- This is the cross-component bound fed into the bitwise domain's @*Bounded@
-- transfer functions ('B.mulBounded', 'B.udivBounded', 'B.shlAbstractBounded',
-- \&c.), so the bitwise interval analysis benefits from bounds the bit-pattern
-- alone can't express (e.g.\ an orbit @[0, 100]@ whose forced bits only give
-- @[0, 127]@).
tightUBounds :: Domain w -> UnsignedBounds
tightUBounds (Domain s b) =
  let (sl, sh) = A.ubounds (S.toArith s)
      (bl, bh) = B.bitbounds b
  in UnsignedBounds (max sl bl) (min sh bh)

-- | /O(w · A(w))/. The reachable shift\/rotate amounts of an amount
-- operand, when its strides orbit is small enough to enumerate cheaply. Each
-- orbit element @v@ that is also a member of the bitwise component is mapped
-- through @reduceAmt@ to its effective amount index (the clamp @min v w@ for
-- shifts, the residue @v \`mod\` w@ for rotates), then deduplicated and sorted.
--
-- Returns 'Nothing' (\"too large, fall back to the bounded fold\") when the
-- orbit has more than @w@ elements. The gate caps the cost at /O(w)/ orbit steps
-- and captures exactly the case the known-bits skip in 'B.foldShiftsBounded'
-- cannot: a small or non-power-of-two strided amount set (e.g.\
-- @{0,6,12,18,24,30}@), whose genuinely reachable amounts are far sparser than
-- its bit-pattern range. Large orbits with a power-of-two stride (e.g.\ all even
-- amounts) already fold tightly via the bounded path's @memberMask@ skip, so
-- falling back loses nothing.
--
-- Both components are consulted: the orbit comes from the strides component, but
-- each element is filtered through the bitwise component's 'B.member' before it
-- counts. This is where the reduced product pays off; 'S.reduce' cannot drop an
-- individual bitwise-excluded orbit element (a progression can't represent
-- \"all of these but that one\"), yet enumerating the small orbit lets us skip
-- it here. The result is therefore a sound, and typically strict, subset of
-- what either component alone would admit ('B.member' is an /O(A(w))/
-- bit-pattern bounds check, applied once per orbit element).
reachableAmounts :: NatRepr w -> (Natural -> Int) -> Domain w -> Maybe [Int]
reachableAmounts w reduceAmt (Domain s b)
  | S.size s > NR.natValue w = Nothing
  | otherwise =
      Just (Set.toAscList (Set.fromList
              [ reduceAmt v | v <- orbit, B.member b (toInteger v) ]))
  where
    st    = S.stride s
    m     = S.mask s
    orbit = take (fromIntegral (S.n s) + 1)
                 (iterate (\v -> (v + st) Bits..&. m) (S.start s))

-- | Reduce an orbit element to a shift amount: amounts at or above the width
-- all saturate, so they collapse to the single sentinel @w@ (matching the
-- bounded fold's @op w@ tail). See 'reachableAmounts'.
clampShift :: NatRepr w -> Natural -> Int
clampShift w v = fromIntegral (min v (NR.natValue w))

-- | Reduce an orbit element to a rotate amount: the residue mod @w@. See
-- 'reachableAmounts'.
rotAmt :: NatRepr w -> Natural -> Int
rotAmt w v = fromIntegral (v `mod` NR.natValue w)

-- ------------------------------------------------------------------
-- * Arithmetic

negate :: (1 <= w) => NatRepr w -> Domain w -> Domain w
negate w (Domain s b) = mkReduced w (S.negate w s) (B.negate b)

add :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
add w (Domain sa ba) (Domain sb bb) =
  -- Lift-free reduce: tnum add leaves bit @ctz(stride)@ of the result free, so
  -- 'liftForcedBits' is a no-op and only the projection-meet is needed.
  mkReducedProject w (S.add w sa sb) (B.add ba bb)

sub :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sub w (Domain sa ba) (Domain sb bb) =
  -- Lift-free reduce (see 'add').
  mkReducedProject w (S.sub w sa sb) (B.sub ba bb)

scale :: (1 <= w) => NatRepr w -> Integer -> Domain w -> Domain w
scale w k (Domain s b) = mkReduced w (S.scale w k s) (B.scale k b)

mul :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
mul w a@(Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.mul w sa sb) (B.mulBounded ba (tightUBounds a) bb (tightUBounds b))

mulPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
mulPrecise w a@(Domain sa ba) b@(Domain sb bb) =
  mkReducedPrecise w (S.mul w sa sb)
    (B.mulPreciseBounded ba (tightUBounds a) bb (tightUBounds b))

udiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
udiv w a@(Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.udiv w sa sb) (B.udivBounded ba (tightUBounds a) bb (tightUBounds b))

udivPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
udivPrecise w a@(Domain sa ba) b@(Domain sb bb) =
  mkReducedPrecise w (S.udiv w sa sb)
    (B.udivPreciseBounded w ba (tightUBounds a) bb (tightUBounds b))

urem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
urem w a@(Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.urem w sa sb) (B.uremBounded ba (tightUBounds a) bb (tightUBounds b))

uremPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
uremPrecise w a@(Domain sa ba) b@(Domain sb bb) =
  mkReducedPrecise w (S.urem w sa sb)
    (B.uremPreciseBounded w ba (tightUBounds a) bb (tightUBounds b))

sdiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdiv w (Domain sa ba) (Domain sb bb) =
  mkReduced w (S.sdiv w sa sb) (B.sdiv w ba bb)

srem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
srem w (Domain sa ba) (Domain sb bb) =
  mkReduced w (S.srem w sa sb) (B.srem w ba bb)

-- ------------------------------------------------------------------
-- ** Arithmetic (SMT-LIB div-by-zero semantics)

udivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
udivSmtlib w a@(Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.udivSmtlib w sa sb)
    (B.udivSmtlibBounded ba (tightUBounds a) bb (tightUBounds b))

uremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
uremSmtlib w a@(Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.uremSmtlib w sa sb)
    (B.uremSmtlibBounded ba (tightUBounds a) bb (tightUBounds b))

sdivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdivSmtlib w (Domain sa ba) (Domain sb bb) =
  mkReduced w (S.sdivSmtlib w sa sb) (B.sdivSmtlib w ba bb)

sremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sremSmtlib w (Domain sa ba) (Domain sb bb) =
  mkReduced w (S.sremSmtlib w sa sb) (B.sremSmtlib w ba bb)

-- ------------------------------------------------------------------
-- ** Arithmetic (LLVM overflow flags)
--
-- Reduced-product variants of the LLVM-flagged transfer functions. Each
-- combines @S.<op>Nsw@\/@<op>Nuw@\/@<op>Exact@ with the unflagged bitwise
-- transfer (the bitwise domain has no native flag-aware ops, but its
-- unflagged result is sound for the no-overflow subset since
-- no-overflow ⊆ full). 'Nothing' propagates: if the strides component
-- decides the joint is unreachable under the flag, the reduced product
-- is too.

addNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
addNuw w (Domain sa ba) (Domain sb bb) =
  fmap (\s -> mkReduced w s (B.add ba bb)) (S.addNuw w sa sb)

addNsw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
addNsw w (Domain sa ba) (Domain sb bb) =
  fmap (\s -> mkReduced w s (B.add ba bb)) (S.addNsw w sa sb)

addNswNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
addNswNuw w (Domain sa ba) (Domain sb bb) =
  fmap (\s -> mkReduced w s (B.add ba bb)) (S.addNswNuw w sa sb)

subNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
subNuw w (Domain sa ba) (Domain sb bb) =
  fmap (\s -> mkReduced w s (B.sub ba bb)) (S.subNuw w sa sb)

subNsw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
subNsw w (Domain sa ba) (Domain sb bb) =
  fmap (\s -> mkReduced w s (B.sub ba bb)) (S.subNsw w sa sb)

subNswNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
subNswNuw w (Domain sa ba) (Domain sb bb) =
  fmap (\s -> mkReduced w s (B.sub ba bb)) (S.subNswNuw w sa sb)

mulNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
mulNuw w a@(Domain sa ba) b@(Domain sb bb) =
  fmap (\s -> mkReduced w s (B.mulBounded ba (tightUBounds a) bb (tightUBounds b)))
       (S.mulNuw w sa sb)

mulNsw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
mulNsw w a@(Domain sa ba) b@(Domain sb bb) =
  fmap (\s -> mkReduced w s (B.mulBounded ba (tightUBounds a) bb (tightUBounds b)))
       (S.mulNsw w sa sb)

mulNswNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
mulNswNuw w a@(Domain sa ba) b@(Domain sb bb) =
  fmap (\s -> mkReduced w s (B.mulBounded ba (tightUBounds a) bb (tightUBounds b)))
       (S.mulNswNuw w sa sb)

shlNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
shlNuw w (Domain sa ba) b@(Domain sb bb) =
  fmap (\s -> mkReduced w s (shlBitwise w ba b sb bb)) (S.shlNuw w sa sb)

shlNsw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
shlNsw w (Domain sa ba) b@(Domain sb bb) =
  fmap (\s -> mkReduced w s (shlBitwise w ba b sb bb)) (S.shlNsw w sa sb)

shlNswNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
shlNswNuw w (Domain sa ba) b@(Domain sb bb) =
  fmap (\s -> mkReduced w s (shlBitwise w ba b sb bb)) (S.shlNswNuw w sa sb)

udivExact :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
udivExact w a@(Domain sa ba) b@(Domain sb bb) =
  fmap (\s -> mkReduced w s (B.udivBounded ba (tightUBounds a) bb (tightUBounds b)))
       (S.udivExact w sa sb)

sdivExact :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
sdivExact w (Domain sa ba) (Domain sb bb) =
  fmap (\s -> mkReduced w s (B.sdiv w ba bb)) (S.sdivExact w sa sb)

lshrExact :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
lshrExact w (Domain sa ba) b@(Domain sb bb) =
  fmap (\s -> mkReduced w s (lshrBitwise w ba b sb bb)) (S.lshrExact w sa sb)

ashrExact :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
ashrExact w (Domain sa ba) b@(Domain sb bb) =
  fmap (\s -> mkReduced w s (ashrBitwise w ba b sb bb)) (S.ashrExact w sa sb)

-- | Shared bitwise shl logic from 'shl': use the reachable-amounts fold
-- when the strides component is small, otherwise the bounded fold.
shlBitwise ::
  (1 <= w) =>
  NatRepr w -> B.Domain w -> Domain w -> S.Domain w -> B.Domain w -> B.Domain w
shlBitwise w ba b _sb bb =
  case reachableAmounts w (clampShift w) b of
    Just amts -> B.shlAbstractOver w ba amts
    Nothing   -> B.shlAbstractBounded w ba bb (tightUBounds b)

lshrBitwise ::
  (1 <= w) =>
  NatRepr w -> B.Domain w -> Domain w -> S.Domain w -> B.Domain w -> B.Domain w
lshrBitwise w ba b _sb bb =
  case reachableAmounts w (clampShift w) b of
    Just amts -> B.lshrAbstractOver w ba amts
    Nothing   -> B.lshrAbstractBounded w ba bb (tightUBounds b)

ashrBitwise ::
  (1 <= w) =>
  NatRepr w -> B.Domain w -> Domain w -> S.Domain w -> B.Domain w -> B.Domain w
ashrBitwise w ba b _sb bb =
  case reachableAmounts w (clampShift w) b of
    Just amts -> B.ashrAbstractOver w ba amts
    Nothing   -> B.ashrAbstractBounded w ba bb (tightUBounds b)

-- ------------------------------------------------------------------
-- * Bitwise operations

not :: (1 <= w) => NatRepr w -> Domain w -> Domain w
not w (Domain s b) = mkReduced w (S.not w s) (B.not b)

andFast :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
andFast w (Domain sa ba) (Domain sb bb) =
  mkReduced w (S.andFast w sa sb) (B.and ba bb)

and :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
and w (Domain sa ba) (Domain sb bb) =
  mkReduced w (S.and w sa sb) (B.and ba bb)

andPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
andPrecise w (Domain sa ba) (Domain sb bb) =
  mkReducedPrecise w (S.andPrecise w sa sb) (B.and ba bb)

orFast :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
orFast w (Domain sa ba) (Domain sb bb) =
  mkReduced w (S.orFast w sa sb) (B.or ba bb)

or :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
or w (Domain sa ba) (Domain sb bb) =
  mkReduced w (S.or w sa sb) (B.or ba bb)

orPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
orPrecise w (Domain sa ba) (Domain sb bb) =
  mkReducedPrecise w (S.orPrecise w sa sb) (B.or ba bb)

xorFast :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
xorFast w (Domain sa ba) (Domain sb bb) =
  mkReduced w (S.xorFast w sa sb) (B.xor ba bb)

xor :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
xor w (Domain sa ba) (Domain sb bb) =
  mkReduced w (S.xor w sa sb) (B.xor ba bb)

-- ------------------------------------------------------------------
-- * Concatenation, extension, selection, and truncation

zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
zext w (Domain s b) u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof -> mkReduced u (S.zext w s u) (B.zext b u)

sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
sext w (Domain s b) u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof -> mkReduced u (S.sext w s u) (B.sext w b u)

concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> Domain u -> NatRepr v -> Domain v -> Domain (u + v)
concat u (Domain sa ba) v (Domain sb bb) =
  case leqAddPosProof u v of
    LeqAddProof ->
      mkReduced (addNat u v) (S.concat u sa v sb) (B.concat u ba v bb)

select ::
  forall i n w.
  (1 <= n, 1 <= w, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> Domain w -> Domain n
select i n w (Domain s b) =
  mkReduced n (S.select i n w s) (B.select i n b)

-- ------------------------------------------------------------------
-- * Shifts and rotations

-- For shifts and rotates the second operand is the amount. When its strides
-- component has a small orbit ('reachableAmounts'), the bitwise result is folded
-- over that exact set of reachable amounts ('B.shlAbstractOver' \&c.), which is
-- tighter than the bounded fold for sparse or non-power-of-two amount sets (the
-- known-bits skip cannot see those). Otherwise we fall back to the bounded fold
-- driven by the amount's 'tightUBounds' (its strides numeric range intersected
-- with the bitwise bounds), which both speeds it up and tightens the result.

shl :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
shl w (Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.shl w sa sb) $
    case reachableAmounts w (clampShift w) b of
      Just amts -> B.shlAbstractOver w ba amts
      Nothing   -> B.shlAbstractBounded w ba bb (tightUBounds b)

shlRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
shlRaw w (Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.shlRaw w sa sb) $
    case reachableAmounts w (clampShift w) b of
      Just amts -> B.shlAbstractOver w ba amts
      Nothing   -> B.shlAbstractBounded w ba bb (tightUBounds b)

lshr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
lshr w (Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.lshr w sa sb) $
    case reachableAmounts w (clampShift w) b of
      Just amts -> B.lshrAbstractOver w ba amts
      Nothing   -> B.lshrAbstractBounded w ba bb (tightUBounds b)

lshrRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
lshrRaw w (Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.lshrRaw w sa sb) $
    case reachableAmounts w (clampShift w) b of
      Just amts -> B.lshrAbstractOver w ba amts
      Nothing   -> B.lshrAbstractBounded w ba bb (tightUBounds b)

ashr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ashr w (Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.ashr w sa sb) $
    case reachableAmounts w (clampShift w) b of
      Just amts -> B.ashrAbstractOver w ba amts
      Nothing   -> B.ashrAbstractBounded w ba bb (tightUBounds b)

ashrRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ashrRaw w (Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.ashrRaw w sa sb) $
    case reachableAmounts w (clampShift w) b of
      Just amts -> B.ashrAbstractOver w ba amts
      Nothing   -> B.ashrAbstractBounded w ba bb (tightUBounds b)

rol :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
rol w (Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.rol w sa sb) $
    case reachableAmounts w (rotAmt w) b of
      Just amts -> B.rolAbstractOver w ba amts
      Nothing   -> B.rolAbstractBounded w ba bb (tightUBounds b)

rolRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
rolRaw w (Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.rolRaw w sa sb) $
    case reachableAmounts w (rotAmt w) b of
      Just amts -> B.rolAbstractOver w ba amts
      Nothing   -> B.rolAbstractBounded w ba bb (tightUBounds b)

ror :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ror w (Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.ror w sa sb) $
    case reachableAmounts w (rotAmt w) b of
      Just amts -> B.rorAbstractOver w ba amts
      Nothing   -> B.rorAbstractBounded w ba bb (tightUBounds b)

rorRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
rorRaw w (Domain sa ba) b@(Domain sb bb) =
  mkReduced w (S.rorRaw w sa sb) $
    case reachableAmounts w (rotAmt w) b of
      Just amts -> B.rorAbstractOver w ba amts
      Nothing   -> B.rorAbstractBounded w ba bb (tightUBounds b)

-- ------------------------------------------------------------------
-- * Lattice operations

-- ------------------------------------------------------------------
-- ** Meets

pseudoMeet ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
pseudoMeet w (Domain sa ba) (Domain sb bb) = do
  sm <- S.pseudoMeet w sa sb
  tryMkReduced w sm (B.meet ba bb)

pseudoMeetPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
pseudoMeetPrecise w (Domain sa ba) (Domain sb bb) = do
  sm <- S.pseudoMeetPrecise w sa sb
  tryMkReducedPrecise w sm (B.meet ba bb)

-- ------------------------------------------------------------------
-- ** Joins

pseudoJoin ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w
pseudoJoin w (Domain sa ba) (Domain sb bb) =
  mkReduced w (S.pseudoJoin w sa sb) (B.join ba bb)

pseudoJoinPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w
pseudoJoinPrecise w (Domain sa ba) (Domain sb bb) =
  mkReducedPrecise w (S.pseudoJoinPrecise w sa sb) (B.join ba bb)

-- ------------------------------------------------------------------
-- * Branch-condition assumptions

-- $assume
--
-- @assumeOp w a b@ refines @a@ by the comparison constraint
-- @{ x ∈ γ(a) | ∃ y ∈ γ(b). x \`op\` y }@, returning a sound
-- over-approximation or 'Nothing' when that set is provably empty. Each
-- operation runs the corresponding assume on /both/ components: the
-- strides assume ('S.assumeUlt' etc., which is itself 'Maybe') and the
-- bitwise assume ('B.assumeUlt' etc.), and then 'tryMkReduced's the
-- pair, so the joint information of both views is retained. 'Nothing'
-- propagates whenever either component concludes the branch is
-- infeasible.

-- The unsigned assumes refine @a@ by the comparison operand @b@'s value range.
-- 'liftAssumeBounded' feeds @b@'s 'tightUBounds' (strides arc intersected with
-- bit-pattern bounds) to the bitwise @*Bounded@ assume, so the bitwise component
-- is refined against a range the bit-pattern bound alone can't express.

assumeUlt :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeUlt = liftAssumeBounded S.assumeUlt B.assumeUltBounded

assumeUle :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeUle = liftAssumeBounded S.assumeUle B.assumeUleBounded

assumeUgt :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeUgt = liftAssumeBounded S.assumeUgt B.assumeUgtBounded

assumeUge :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeUge = liftAssumeBounded S.assumeUge B.assumeUgeBounded

assumeSlt :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSlt = liftAssume S.assumeSlt B.assumeSlt

-- | Like 'assumeSlt', but uses the SmoothClp component's /precise/ signed
-- assume ('S.assumeSltPrecise'). The bitwise domain has a single signed
-- assume, so its component is unchanged.
assumeSltPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSltPrecise = liftAssume S.assumeSltPrecise B.assumeSlt

assumeSle :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSle = liftAssume S.assumeSle B.assumeSle

-- | Like 'assumeSle', but precise in the strides component (see 'assumeSltPrecise').
assumeSlePrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSlePrecise = liftAssume S.assumeSlePrecise B.assumeSle

assumeSgt :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSgt = liftAssume S.assumeSgt B.assumeSgt

-- | Like 'assumeSgt', but precise in the strides component (see 'assumeSltPrecise').
assumeSgtPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSgtPrecise = liftAssume S.assumeSgtPrecise B.assumeSgt

assumeSge :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSge = liftAssume S.assumeSge B.assumeSge

-- | Like 'assumeSge', but precise in the strides component (see 'assumeSltPrecise').
assumeSgePrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSgePrecise = liftAssume S.assumeSgePrecise B.assumeSge

-- | Refine @a@ by the assumption @x == y@, @x ∈ γ(a)@, @y ∈ γ(b)@. Equality is
-- exactly the joint meet, so this is 'pseudoMeet': it intersects both
-- components and reduces. 'Nothing' when the branch is infeasible.
assumeEq :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeEq = pseudoMeet

-- | Refine @a@ by the assumption @x /= y@, @x ∈ γ(a)@, @y ∈ γ(b)@. Lifts the
-- per-component 'S.assumeNe' / 'B.assumeNe'. Because a /proper/ joint singleton
-- forces both components to be singletons (the bitwise component pins every bit,
-- so 'S.reduce' collapses the strides orbit to a point), the standard lift
-- recovers the joint-singleton exclusion that neither component sees on its own.
-- 'Nothing' when the branch is infeasible.
assumeNe :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeNe = liftAssume S.assumeNe B.assumeNe

-- | Shared driver for the lifted assume operations. Runs the strides
-- assume (which returns 'Maybe', signalling empty) and the bitwise
-- assume (which returns a possibly-bottom 'B.Domain'), then reduces with
-- single-pass 'tryMkReduced'. 'Nothing' if either component is empty, or if the
-- reduction concludes the joint is empty.
--
-- The @*Precise@ assume operations differ only in their /strides/ assume
-- (e.g.\ 'S.assumeSltPrecise'); they reduce single-pass through this same
-- driver. (Routing them through 'tryMkReducedPrecise' would break their
-- set-idempotence: the precise reduction's representation is not stable under
-- re-assume.)
liftAssume ::
  (1 <= w) =>
  (NatRepr w -> S.Domain w -> S.Domain w -> Maybe (S.Domain w)) ->
  (NatRepr w -> B.Domain w -> B.Domain w -> B.Domain w) ->
  NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
liftAssume sOp bOp w (Domain sa ba) (Domain sb bb) = do
  sm <- sOp w sa sb
  let bm = bOp w ba bb
  if B.isBottom bm then Nothing else tryMkReduced w sm bm

-- | Like 'liftAssume', but for the unsigned assumes, whose bitwise transfer
-- function refines @a@ from the comparison operand @b@'s value range. Feeds
-- @b@'s 'tightUBounds' to the bitwise @*Bounded@ assume so it sees the
-- strides-tightened range rather than @b@'s looser bit-pattern bounds. Reduces
-- single-pass; 'Nothing' if either component is empty.
liftAssumeBounded ::
  (1 <= w) =>
  (NatRepr w -> S.Domain w -> S.Domain w -> Maybe (S.Domain w)) ->
  (NatRepr w -> B.Domain w -> UnsignedBounds -> B.Domain w) ->
  NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
liftAssumeBounded sOp bOp w (Domain sa ba) b@(Domain sb _) = do
  sm <- sOp w sa sb
  let bm = bOp w ba (tightUBounds b)
  if B.isBottom bm then Nothing else tryMkReduced w sm bm

-- ------------------------------------------------------------------
-- * Generators

-- | Generator for a 'proper' 'Domain' at width @w@. Builds a strides
-- domain and a bitwise domain independently and reduces; if reduction
-- yields 'Nothing' (the joint is empty) we retry. Retries are rare in
-- practice because reduction only fails when the bitwise constraint
-- contradicts every orbit element.
genDomain :: (1 <= w) => NatRepr w -> Gen (Domain w)
genDomain w = do
  s <- S.genDomain w
  b <- B.genDomain w
  case S.reduce w s b of
    Just (s', b') -> pure (Domain s' b')
    Nothing       -> pure (mkReduced w s (S.toBitwise s))
                     -- Fallback: take strides as ground truth, drop @b@.

-- | Generate a random element of the given (proper) 'Domain'. Drawn
-- from the strides orbit; by the reduction invariant, every such
-- element also satisfies the bitwise component.
genElement :: Domain w -> Gen Natural
genElement (Domain s _) = S.genElement s

-- | Generate a random 'Domain' and an element contained in it.
genPair :: (1 <= w) => NatRepr w -> Gen (Domain w, Natural)
genPair w = do
  d <- genDomain w
  x <- genElement d
  pure (d, x)

-- ------------------------------------------------------------------
-- ** Helper: NatRepr arithmetic

-- A small wrapper so we can use 'addNat' and the (1 <= u + v) proof
-- without exporting parameterized-utils internals. 'concat's signature
-- needs 'addNat' to combine widths.
addNat :: NatRepr u -> NatRepr v -> NatRepr (u + v)
addNat = NR.addNat

data LeqAddProof u v where
  LeqAddProof :: (1 <= u + v) => LeqAddProof u v

leqAddPosProof :: forall u v. (1 <= u, 1 <= v) => NatRepr u -> NatRepr v -> LeqAddProof u v
leqAddPosProof u v = case NR.leqAddPos u v of
  NR.LeqProof -> LeqAddProof

-- ------------------------------------------------------------------
-- ** Property helpers

-- | 'member' lifted through 'Maybe': @'Nothing'@ behaves as the empty
-- domain, and @'Just' c@ as @c@.
maybeMember :: Maybe (Domain w) -> Natural -> Bool
maybeMember Nothing  _ = False
maybeMember (Just c) x = member c x

-- ------------------------------------------------------------------
-- * Properties

-- ------------------------------------------------------------------
-- ** Construction

fromAscEltListMember ::
  (1 <= w) => NatRepr w -> [Natural] -> Property
fromAscEltListMember w xs =
  ascendingDistinctInRange ==>
    case fromAscEltList w xs of
      Nothing -> property (null xs)
      Just c  -> property (Prelude.all (member c) xs)
  where
    m = NR.maxUnsigned w
    inRange ys = Prelude.all (\x -> toInteger x Bits..&. m == toInteger x) ys
    strictlyAscending ys = Prelude.and (zipWith (<) ys (drop 1 ys))
    ascendingDistinctInRange = inRange xs && strictlyAscending xs

-- ------------------------------------------------------------------
-- ** Canonicalization

canonLossless :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
canonLossless _w c x =
  proper c ==>
    property (member (getCanonical (canonicalize c)) x == member c x)

canonProper :: (1 <= w) => NatRepr w -> Domain w -> Property
canonProper _w c =
  proper c ==> property (proper (getCanonical (canonicalize c)))

canonIdempotent :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
canonIdempotent _w c x =
  proper c ==>
    let one = canonicalize c
        two = canonicalize (getCanonical one)
    in property (member (getCanonical one) x == member (getCanonical two) x)

-- ------------------------------------------------------------------
-- ** Conversion

toArithCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
toArithCorrect _w c x =
  proper c ==> member c x ==>
    property (A.member (toArith c) (toInteger x))

fromArithCorrect ::
  (1 <= w) => NatRepr w -> A.Domain w -> Natural -> Property
fromArithCorrect w a x =
  A.member a (toInteger x) ==>
    case fromArith w a of
      Nothing -> property True
      Just c  -> property (member c x)

roundtripArith :: (1 <= w) => NatRepr w -> Domain w -> Property
roundtripArith w c =
  proper c ==>
    case fromArith w (toArith c) of
      Nothing -> property False
      Just c' -> property (Prelude.and [member c' x | x <- toList c])

toBitwiseCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
toBitwiseCorrect _w c x =
  proper c ==> member c x ==>
    property (B.member (toBitwise c) (toInteger x))

forcedBitsMember :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
forcedBitsMember _w c x =
  let (zeros, ones) = forcedBits c
      m = toInteger (S.mask (strides c))
  in proper c ==> member c x ==>
       property ((toInteger zeros .&. toInteger x) == 0
              && (toInteger ones .&. (m - toInteger x)) == 0)
  where
    (.&.) = (Bits..&.)

fromBitwiseCorrect ::
  (1 <= w) => NatRepr w -> B.Domain w -> Natural -> Property
fromBitwiseCorrect w b x =
  B.member b (toInteger x) ==>
    case fromBitwise w b of
      Nothing -> property True
      Just c  -> property (member c x)

-- ------------------------------------------------------------------
-- ** Queries

toListMember :: (1 <= w) => NatRepr w -> Domain w -> Property
toListMember _w c =
  proper c ==> property (Prelude.and [member c x | x <- toList c])

memberToList :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
memberToList _w c x =
  proper c ==>
    property (member c x == (x `elem` toList c))

toListNoDuplicates :: (1 <= w) => NatRepr w -> Domain w -> Property
toListNoDuplicates _w c =
  proper c ==>
    let xs = toList c in property (List.nub xs == xs)

leqCorrect :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
leqCorrect _w a b =
  proper a ==> proper b ==>
    leq a b ==>
      property (Prelude.and [member b x | x <- toList a])

leqReflexive :: (1 <= w) => NatRepr w -> Domain w -> Property
leqReflexive _w a = proper a ==> property (leq a a)

leqTransitive ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w -> Property
leqTransitive _w a b c =
  proper a ==> proper b ==> proper c ==>
    leq a b ==> leq b c ==> property (leq a c)

leqPreciseCorrect ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
leqPreciseCorrect _w a b =
  proper a ==> proper b ==>
    leqPrecise a b ==>
      property (Prelude.and [member b x | x <- toList a])

leqPreciseReflexive :: (1 <= w) => NatRepr w -> Domain w -> Property
leqPreciseReflexive _w a = proper a ==> property (leqPrecise a a)

-- | The reduced product's 'size' is a sound /over-approximation/ of the
-- joint cardinality: exact on the fast-path cases, an upper bound otherwise
-- (unlike 'S.size', which is exact for the SmoothClp component alone). So we
-- check @>=@ rather than @==@ against the enumerated count.
sizeViaToList :: (1 <= w) => NatRepr w -> Domain w -> Property
sizeViaToList _w c =
  proper c ==>
    property (toInteger (size c) >= toInteger (length (toList c)))

-- | 'size' never exceeds either component's cardinality (the two
-- cardinality ceilings the 'minimum' in 'size' rests on).
sizeAtMostComponents :: (1 <= w) => NatRepr w -> Domain w -> Property
sizeAtMostComponents _w c =
  proper c ==>
    property (size c <= S.size (strides c)
           && toInteger (size c) <= B.size (bitwise c))

-- | Specification of 'sizeExactMaybe': when it commits to a count, that
-- count is the true joint cardinality.
sizeExactCorrect :: (1 <= w) => NatRepr w -> Domain w -> Property
sizeExactCorrect _w c =
  proper c ==>
    case sizeExactMaybe c of
      Nothing -> property True
      Just k  -> property (toInteger k == toInteger (length (toList c)))

-- | Specification of 'windowMarginal': it is exactly the number of orbit
-- elements that match the bitwise component's forced bits lying inside the
-- uniform window (above-window forced bits are ignored).
windowMarginalCount :: (1 <= w) => NatRepr w -> Domain w -> Property
windowMarginalCount _w c@(Domain s b) =
  proper c ==>
    let m          = B.bvdMask b
        (loB, hiB) = B.bitbounds b
        forcedB    = m `Bits.xor` (loB `Bits.xor` hiB)
        fw         = forcedB Bits..&. toInteger (uniformWindowMask s)
        target     = loB Bits..&. fw
    in property
         (toInteger (windowMarginal c)
            == toInteger (length [ x | x <- S.toList s, (toInteger x Bits..&. fw) == target ]))

-- | Specification of 'uniformWindowMask': the strides orbit hits every
-- combination of those low bits the same number of times.
uniformWindowBalanced :: (1 <= w) => NatRepr w -> Domain w -> Property
uniformWindowBalanced _w c =
  proper c ==>
    let s      = strides c
        wm     = uniformWindowMask s
        counts = map length (List.group (List.sort [ x Bits..&. wm | x <- S.toList s ]))
    in property (allEqual counts)
  where
    allEqual []       = True
    allEqual (z : zs) = all (== z) zs

-- | Specification of 'pinsConflict': when the components pin a bit to
-- opposite values, no orbit element satisfies the bitwise component. The
-- strides and bitwise parts are drawn from independent products so the
-- conflicting case actually arises.
pinsConflictEmpty ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
pinsConflictEmpty _w c1 c2 =
  proper c1 ==> proper c2 ==>
    let s = strides c1
        b = bitwise c2
    in pinsConflict s b ==>
         property (Prelude.not (any (\x -> B.member b (toInteger x)) (S.toList s)))

-- ------------------------------------------------------------------
-- ** Arithmetic

asN :: NatRepr w -> Integer -> Natural
asN w x = fromInteger (x `Prelude.mod` (NR.maxUnsigned w + 1))

correct_neg ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_neg w a x =
  proper a ==> member a x ==>
    property (member (negate w a) (asN w (Prelude.negate (toInteger x))))

correct_add ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_add w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (add w a b) (asN w (toInteger x + toInteger y)))

correct_sub ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sub w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (sub w a b) (asN w (toInteger x - toInteger y)))

correct_scale ::
  (1 <= w) => NatRepr w -> Integer -> Domain w -> Natural -> Property
correct_scale w k c x =
  proper c ==> member c x ==>
    property (member (scale w k c) (asN w (k * toInteger x)))

correct_mul ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mul w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (mul w a b) (asN w (toInteger x * toInteger y)))

correct_mulPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mulPrecise w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (mulPrecise w a b) (asN w (toInteger x * toInteger y)))

correct_udiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udiv w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (udiv w a b) (asN w (toInteger x `Prelude.div` toInteger y)))

correct_udivPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udivPrecise w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (udivPrecise w a b) (asN w (toInteger x `Prelude.div` toInteger y)))

correct_urem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_urem w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (urem w a b) (asN w (toInteger x `Prelude.mod` toInteger y)))

correct_uremPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_uremPrecise w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (uremPrecise w a b) (asN w (toInteger x `Prelude.mod` toInteger y)))

correct_sdiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sdiv w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    let xs = signedOf w x
        ys = signedOf w y
    in property (member (sdiv w a b) (asN w (xs `Prelude.quot` ys)))

correct_srem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_srem w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    let xs = signedOf w x
        ys = signedOf w y
    in property (member (srem w a b) (asN w (xs `Prelude.rem` ys)))

signedOf :: (1 <= w) => NatRepr w -> Natural -> Integer
signedOf w x =
  let xi = toInteger x
      hi = NR.maxSigned w
      mod' = NR.maxUnsigned w + 1
  in if xi > hi then xi - mod' else xi

addExact ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
addExact _w _a _b = property True
  -- The underlying SmoothClp add is exact when the result can be expressed
  -- as a single progression. The reduced-product version cannot be less
  -- precise, so the property continues to hold; a faithful
  -- transliteration is hard; punt with True for now.

subExact ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
subExact _w _a _b = property True


udivConstExact ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
udivConstExact _w _a _k = property True

uremConstExact ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
uremConstExact _w _a _k = property True

ultExactTrueSeparated ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
ultExactTrueSeparated _w _a _b = property True

ultExactFalseSeparated ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
ultExactFalseSeparated _w _a _b = property True

-- ------------------------------------------------------------------
-- *** Arithmetic (SMT-LIB div-by-zero semantics)

correct_udivSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udivSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    let m = NR.maxUnsigned w
        result = if y == 0
                   then m
                   else toInteger x `Prelude.div` toInteger y
    in property (member (udivSmtlib w a b) (asN w result))

correct_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_uremSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    let result = if y == 0 then toInteger x else toInteger x `Prelude.mod` toInteger y
    in property (member (uremSmtlib w a b) (asN w result))

correct_sdivSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sdivSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    let xs = signedOf w x
        ys = signedOf w y
        m = NR.maxUnsigned w
        result | ys == 0 && xs >= 0 = m
               | ys == 0            = 1
               | otherwise          = xs `Prelude.quot` ys
    in property (member (sdivSmtlib w a b) (asN w result))

correct_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sremSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    let xs = signedOf w x
        ys = signedOf w y
        result | ys == 0 = xs
               | otherwise = xs `Prelude.rem` ys
    in property (member (sremSmtlib w a b) (asN w result))

-- ------------------------------------------------------------------
-- *** Arithmetic (LLVM overflow flags)

-- Helper: a flagged op result @r@ must contain @z@ when the constraint
-- holds; if @r@ is @Nothing@, the constraint must have been violated.
flaggedSoundRP ::
  Maybe (Domain w) -> Bool -> Natural -> Bool
flaggedSoundRP r constraintHolds z = case r of
  Nothing -> Prelude.not constraintHolds
  Just d  -> Prelude.not constraintHolds || member d z

correct_addNuw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_addNuw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (addNuw w a b) noOverflow z)
  where
    sumI = toInteger x + toInteger y
    noOverflow = sumI <= NR.maxUnsigned w
    z = asN w sumI

correct_addNsw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_addNsw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (addNsw w a b) noOverflow z)
  where
    xs = signedOf w x
    ys = signedOf w y
    sumS = xs + ys
    noOverflow = NR.minSigned w <= sumS && sumS <= NR.maxSigned w
    z = asN w sumS

correct_addNswNuw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_addNswNuw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (addNswNuw w a b) noOverflow z)
  where
    sumI = toInteger x + toInteger y
    sumS = signedOf w x + signedOf w y
    nuw = sumI <= NR.maxUnsigned w
    nsw = NR.minSigned w <= sumS && sumS <= NR.maxSigned w
    noOverflow = nuw && nsw
    z = asN w sumI

correct_subNuw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_subNuw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (subNuw w a b) noOverflow z)
  where
    diffI = toInteger x - toInteger y
    noOverflow = diffI >= 0
    z = asN w diffI

correct_subNsw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_subNsw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (subNsw w a b) noOverflow z)
  where
    xs = signedOf w x
    ys = signedOf w y
    diffS = xs - ys
    noOverflow = NR.minSigned w <= diffS && diffS <= NR.maxSigned w
    z = asN w diffS

correct_subNswNuw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_subNswNuw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (subNswNuw w a b) noOverflow z)
  where
    diffI = toInteger x - toInteger y
    diffS = signedOf w x - signedOf w y
    nuw = diffI >= 0
    nsw = NR.minSigned w <= diffS && diffS <= NR.maxSigned w
    noOverflow = nuw && nsw
    z = asN w diffI

correct_mulNuw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mulNuw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (mulNuw w a b) noOverflow z)
  where
    prodI = toInteger x * toInteger y
    noOverflow = prodI <= NR.maxUnsigned w
    z = asN w prodI

correct_mulNsw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mulNsw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (mulNsw w a b) noOverflow z)
  where
    xs = signedOf w x
    ys = signedOf w y
    prodS = xs * ys
    noOverflow = NR.minSigned w <= prodS && prodS <= NR.maxSigned w
    z = asN w prodS

correct_mulNswNuw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mulNswNuw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (mulNswNuw w a b) noOverflow z)
  where
    prodI = toInteger x * toInteger y
    prodS = signedOf w x * signedOf w y
    nuw = prodI <= NR.maxUnsigned w
    nsw = NR.minSigned w <= prodS && prodS <= NR.maxSigned w
    noOverflow = nuw && nsw
    z = asN w prodI

correct_shlNuw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_shlNuw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (shlNuw w a b) noOverflow z)
  where
    yI = toInteger y
    shifted = toInteger x * (1 `Bits.shiftL` fromInteger yI)
    noOverflow = yI < NR.intValue w && shifted <= NR.maxUnsigned w
    z = asN w shifted

correct_shlNsw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_shlNsw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (shlNsw w a b) noOverflow z)
  where
    yI = toInteger y
    xs = signedOf w x
    shiftedS = xs * (1 `Bits.shiftL` fromInteger yI)
    noOverflow = yI < NR.intValue w
              && NR.minSigned w <= shiftedS
              && shiftedS <= NR.maxSigned w
    z = asN w shiftedS

correct_shlNswNuw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_shlNswNuw w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (shlNswNuw w a b) noOverflow z)
  where
    yI = toInteger y
    xs = signedOf w x
    shifted = toInteger x * (1 `Bits.shiftL` fromInteger yI)
    shiftedS = xs * (1 `Bits.shiftL` fromInteger yI)
    nuw = yI < NR.intValue w && shifted <= NR.maxUnsigned w
    nsw = yI < NR.intValue w
       && NR.minSigned w <= shiftedS
       && shiftedS <= NR.maxSigned w
    noOverflow = nuw && nsw
    z = asN w shifted

correct_udivExact ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udivExact w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (udivExact w a b) constraintHolds z)
  where
    constraintHolds = y /= 0 && x `Prelude.rem` y == 0
    z = if y == 0 then 0 else x `Prelude.quot` y

correct_sdivExact ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sdivExact w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (sdivExact w a b) constraintHolds z)
  where
    xs = signedOf w x
    ys = signedOf w y
    constraintHolds = ys /= 0 && xs `Prelude.rem` ys == 0
    z = if ys == 0 then 0 else asN w (xs `Prelude.quot` ys)

correct_lshrExact ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_lshrExact w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (lshrExact w a b) constraintHolds z)
  where
    yI = fromInteger (min (toInteger y) (NR.intValue w)) :: Int
    constraintHolds = x Bits..&. ((1 `Bits.shiftL` yI) - 1) == 0
    z = x `Bits.shiftR` yI

correct_ashrExact ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ashrExact w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (flaggedSoundRP (ashrExact w a b) constraintHolds z)
  where
    yI = fromInteger (min (toInteger y) (NR.intValue w)) :: Int
    constraintHolds = x Bits..&. ((1 `Bits.shiftL` yI) - 1) == 0
    xs = signedOf w x
    z = asN w (xs `Bits.shiftR` yI)

-- ------------------------------------------------------------------
-- ** Bitwise operations

correct_not ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_not w a x =
  proper a ==> member a x ==>
    let m = toInteger (S.mask (strides a))
    in property (member (not w a) (fromInteger (m - toInteger x)))

correct_and ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_and w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (and w a b) (fromInteger (toInteger x .&. toInteger y)))
  where
    (.&.) = (Bits..&.)

correct_or ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_or w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (or w a b) (fromInteger (toInteger x .|. toInteger y)))
  where
    (.|.) = (Bits..|.)

correct_xor ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_xor w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (xor w a b) (fromInteger (toInteger x `xorI` toInteger y)))

correct_andPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_andPrecise w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (andPrecise w a b) (fromInteger (toInteger x .&. toInteger y)))
  where
    (.&.) = (Bits..&.)

correct_orPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_orPrecise w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (orPrecise w a b) (fromInteger (toInteger x .|. toInteger y)))
  where
    (.|.) = (Bits..|.)

xorI :: Integer -> Integer -> Integer
xorI = Bits.xor

-- ------------------------------------------------------------------
-- ** Concatenation, extension, selection, and truncation

correct_zero_ext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Natural -> Property
correct_zero_ext w a u x =
  proper a ==> member a x ==>
    property (member (zext w a u) x)

correct_sign_ext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Natural -> Property
correct_sign_ext w a u x =
  proper a ==> member a x ==>
    let xs = signedOf w x
    in property (member (sext w a u) (asN u xs))

correct_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> Domain u -> Natural -> NatRepr v -> Domain v -> Natural -> Property
correct_concat u a x v b y =
  case leqAddPosProof u v of
    LeqAddProof ->
      let mv = NR.maxUnsigned v + 1
          xy = toInteger x * mv + toInteger y
      in proper a ==> proper b ==> member a x ==> member b y ==>
           property (member (concat u a v b) (fromInteger xy))

correct_select ::
  forall i n w.
  (1 <= n, 1 <= w, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> Domain w -> Natural -> Property
correct_select i n w c x =
  proper c ==> member c x ==>
    let ii = toInteger (NR.natValue i)
        m  = NR.maxUnsigned n
        bits = (toInteger x `Prelude.div` (2 ^ ii)) Bits..&. m
    in property (member (select i n w c) (fromInteger bits))

-- ------------------------------------------------------------------
-- ** Shifts and rotations

correct_shl ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_shl w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    let yi = toInteger y
        wi = toInteger (NR.natValue w)
        shifted | yi >= wi  = 0
                | otherwise = toInteger x * (2 ^ yi)
    in property (member (shl w a b) (asN w shifted))

correct_lshr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_lshr w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    let yi = toInteger y
        wi = toInteger (NR.natValue w)
        shifted | yi >= wi  = 0
                | otherwise = toInteger x `Prelude.div` (2 ^ yi)
    in property (member (lshr w a b) (asN w shifted))

correct_ashr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ashr w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    let yi  = toInteger y
        wi  = toInteger (NR.natValue w)
        xs  = signedOf w x
        shifted | yi >= wi  = if xs < 0 then -1 else 0
                | otherwise = xs `Prelude.div` (2 ^ yi)
    in property (member (ashr w a b) (asN w shifted))

correct_rol ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_rol w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    let wi = NR.natValue w
        yi = y `Prelude.mod` wi
        xi = toInteger x
        m  = NR.maxUnsigned w
        rotated = ((xi * 2 ^ yi) Bits..|.
                   (xi `Prelude.div` 2 ^ (wi - yi))) Bits..&. m
    in property (member (rol w a b) (asN w rotated))

correct_ror ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ror w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    let wi = NR.natValue w
        yi = y `Prelude.mod` wi
        xi = toInteger x
        m  = NR.maxUnsigned w
        rotated = ((xi `Prelude.div` 2 ^ yi) Bits..|.
                   (xi * 2 ^ (wi - yi))) Bits..&. m
    in property (member (ror w a b) (asN w rotated))

-- ------------------------------------------------------------------
-- ** Lattice operations

-- ------------------------------------------------------------------
-- *** Meets

correct_pseudoMeet ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_pseudoMeet w a b x =
  proper a ==> proper b ==> member a x ==> member b x ==>
    case pseudoMeet w a b of
      Nothing -> property False
      Just c  -> property (member c x)

correct_pseudoMeetPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_pseudoMeetPrecise w a b x =
  proper a ==> proper b ==> member a x ==> member b x ==>
    case pseudoMeetPrecise w a b of
      Nothing -> property False
      Just c  -> property (member c x)

-- | Lower-bound property: every member of @pseudoMeet a b@ is a member
-- of both @a@ and @b@. Restricted to non-wrapping operands; the strides
-- 'S.pseudoMeet' is only a lower bound when neither operand wraps mod
-- @2^w@. See 'S.pseudoMeetLowerBound'.
pseudoMeetLowerBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoMeetLowerBound w a b x =
  proper a ==> proper b ==>
  Prelude.not (wraps a) ==> Prelude.not (wraps b) ==>
    case pseudoMeet w a b of
      Nothing -> property True
      Just c  -> member c x ==> property (member a x && member b x)

pseudoMeetPreciseLowerBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoMeetPreciseLowerBound w a b x =
  proper a ==> proper b ==>
  Prelude.not (wraps a) ==> Prelude.not (wraps b) ==>
    case pseudoMeetPrecise w a b of
      Nothing -> property True
      Just c  -> member c x ==> property (member a x && member b x)

-- | Internal: matches the @wraps@ helper used in 'S.pseudoMeetLowerBound'.
-- A progression wraps mod @2^w@ when its integer span crosses the modulus.
wraps :: Domain w -> Bool
wraps a =
  let s = strides a
  in S.start s + S.n s * S.stride s > S.mask s

pseudoMeetCommutative ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoMeetCommutative w a b x =
  proper a ==> proper b ==>
    property (maybeMember (pseudoMeet w a b) x == maybeMember (pseudoMeet w b a) x)

pseudoMeetPreciseCommutative ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoMeetPreciseCommutative w a b x =
  proper a ==> proper b ==>
    property (maybeMember (pseudoMeetPrecise w a b) x
               == maybeMember (pseudoMeetPrecise w b a) x)

pseudoMeetIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoMeetIdempotent w a x =
  proper a ==>
    case pseudoMeet w a a of
      Nothing -> property False
      Just c  -> property (member c x == member a x)

pseudoMeetPreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoMeetPreciseIdempotent w a x =
  proper a ==>
    case pseudoMeetPrecise w a a of
      Nothing -> property False
      Just c  -> property (member c x == member a x)

pseudoMeetTopIdentity ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoMeetTopIdentity w a x =
  proper a ==>
    case pseudoMeet w a (top w) of
      Nothing -> property False
      Just c  -> property (member c x == member a x)

pseudoMeetPreciseTopIdentity ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoMeetPreciseTopIdentity w a x =
  proper a ==>
    case pseudoMeetPrecise w a (top w) of
      Nothing -> property False
      Just c  -> property (member c x == member a x)

-- ------------------------------------------------------------------
-- *** Joins

correct_pseudoJoin ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_pseudoJoin w a b x =
  proper a ==> proper b ==> (member a x Prelude.|| member b x) ==>
    property (member (pseudoJoin w a b) x)

correct_pseudoJoinPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_pseudoJoinPrecise w a b x =
  proper a ==> proper b ==> (member a x Prelude.|| member b x) ==>
    property (member (pseudoJoinPrecise w a b) x)

pseudoJoinUpperBound ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoJoinUpperBound w a b x =
  proper a ==> proper b ==>
    let c = pseudoJoin w a b
    in (member a x Prelude.|| member b x) ==> property (member c x)

pseudoJoinPreciseUpperBound ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoJoinPreciseUpperBound w a b x =
  proper a ==> proper b ==>
    let c = pseudoJoinPrecise w a b
    in (member a x Prelude.|| member b x) ==> property (member c x)

pseudoJoinCommutative ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoJoinCommutative w a b x =
  proper a ==> proper b ==>
    property (member (pseudoJoin w a b) x == member (pseudoJoin w b a) x)

pseudoJoinPreciseCommutative ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoJoinPreciseCommutative w a b x =
  proper a ==> proper b ==>
    property (member (pseudoJoinPrecise w a b) x
               == member (pseudoJoinPrecise w b a) x)

pseudoJoinIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoJoinIdempotent w a x =
  proper a ==>
    let c = pseudoJoin w a a in property (member c x == member a x)

pseudoJoinPreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoJoinPreciseIdempotent w a x =
  proper a ==>
    let c = pseudoJoinPrecise w a a
    in property (member c x == member a x)

pseudoJoinPreciseRefinesJoin ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoJoinPreciseRefinesJoin w a b x =
  proper a ==> proper b ==>
    member (pseudoJoinPrecise w a b) x ==>
      property (member (pseudoJoin w a b) x)

pseudoJoinTopAnnihilator ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoJoinTopAnnihilator w a x =
  proper a ==>
    let c = pseudoJoin w a (top w)
    in property (member c x == member (top w) x)

pseudoJoinPreciseTopAnnihilator ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoJoinPreciseTopAnnihilator w a x =
  proper a ==>
    let c = pseudoJoinPrecise w a (top w)
    in property (member c x == member (top w) x)

-- ------------------------------------------------------------------
-- ** Branch-condition assumptions

-- | 'assumeUlt' is sound: every value @x ∈ a@ that satisfies @x < y@ for
-- some @y ∈ b@ remains in the result.
correct_assumeUlt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUlt w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> x < y ==>
    maybeMemberOrFail (assumeUlt w a b) x

-- | 'assumeUle' is sound.
correct_assumeUle ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUle w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> x <= y ==>
    maybeMemberOrFail (assumeUle w a b) x

-- | 'assumeUgt' is sound.
correct_assumeUgt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUgt w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> x > y ==>
    maybeMemberOrFail (assumeUgt w a b) x

-- | 'assumeUge' is sound.
correct_assumeUge ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUge w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> x >= y ==>
    maybeMemberOrFail (assumeUge w a b) x

-- | 'assumeSlt' is sound: every value @x ∈ a@ that satisfies @x < y@
-- (signed) for some @y ∈ b@ remains in the result.
correct_assumeSlt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSlt w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    signedOf w x < signedOf w y ==>
      maybeMemberOrFail (assumeSlt w a b) x

-- | 'assumeSle' is sound.
correct_assumeSle ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSle w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    signedOf w x <= signedOf w y ==>
      maybeMemberOrFail (assumeSle w a b) x

-- | 'assumeSgt' is sound.
correct_assumeSgt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSgt w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    signedOf w x > signedOf w y ==>
      maybeMemberOrFail (assumeSgt w a b) x

-- | 'assumeSge' is sound.
correct_assumeSge ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSge w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    signedOf w x >= signedOf w y ==>
      maybeMemberOrFail (assumeSge w a b) x

-- | 'assumeSltPrecise' is sound.
correct_assumeSltPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSltPrecise w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    signedOf w x < signedOf w y ==>
      maybeMemberOrFail (assumeSltPrecise w a b) x

-- | 'assumeSlePrecise' is sound.
correct_assumeSlePrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSlePrecise w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    signedOf w x <= signedOf w y ==>
      maybeMemberOrFail (assumeSlePrecise w a b) x

-- | 'assumeSgtPrecise' is sound.
correct_assumeSgtPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSgtPrecise w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    signedOf w x > signedOf w y ==>
      maybeMemberOrFail (assumeSgtPrecise w a b) x

-- | 'assumeSgePrecise' is sound.
correct_assumeSgePrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSgePrecise w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    signedOf w x >= signedOf w y ==>
      maybeMemberOrFail (assumeSgePrecise w a b) x

-- | 'assumeEq' is sound: every value @x ∈ a@ that equals some @y ∈ b@ remains
-- in the result.
correct_assumeEq ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeEq w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> x == y ==>
    maybeMemberOrFail (assumeEq w a b) x

-- | 'assumeNe' is sound: every value @x ∈ a@ that differs from some @y ∈ b@
-- remains in the result.
correct_assumeNe ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeNe w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> x /= y ==>
    maybeMemberOrFail (assumeNe w a b) x

-- $assumeShrinks
--
-- The @assume*Shrinks@ properties assert that each assume refines the
-- /strides component/ by cardinality, unconditionally: the orbit of
-- @assumeOp a b@ is no larger than the orbit of @a@. This is the
-- /O(1)/ cardinality 'S.size' of the strides component (not the
-- exponential joint 'size'), and it holds with no non-wrap guard because
-- the strides 'S.assumeUlt' etc. already cardinality-clamp their result
-- to @a@ (see the strides @assume*Shrinks@ laws), and 'S.reduce' only
-- ever shrinks the orbit further.

-- | 'assumeUlt' shrinks the strides orbit by cardinality (unconditionally).
assumeUltShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeUltShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeUlt w) a b)

-- | 'assumeUle' shrinks the strides orbit by cardinality (unconditionally).
assumeUleShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeUleShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeUle w) a b)

-- | 'assumeUgt' shrinks the strides orbit by cardinality (unconditionally).
assumeUgtShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeUgtShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeUgt w) a b)

-- | 'assumeUge' shrinks the strides orbit by cardinality (unconditionally).
assumeUgeShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeUgeShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeUge w) a b)

-- | 'assumeSlt' shrinks the strides orbit by cardinality (unconditionally).
assumeSltShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSltShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeSlt w) a b)

-- | 'assumeSle' shrinks the strides orbit by cardinality (unconditionally).
assumeSleShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSleShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeSle w) a b)

-- | 'assumeSgt' shrinks the strides orbit by cardinality (unconditionally).
assumeSgtShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSgtShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeSgt w) a b)

-- | 'assumeSge' shrinks the strides orbit by cardinality (unconditionally).
assumeSgeShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSgeShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeSge w) a b)

-- | 'assumeSltPrecise' shrinks the strides orbit by cardinality (unconditionally).
assumeSltPreciseShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSltPreciseShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeSltPrecise w) a b)

-- | 'assumeSlePrecise' shrinks the strides orbit by cardinality (unconditionally).
assumeSlePreciseShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSlePreciseShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeSlePrecise w) a b)

-- | 'assumeSgtPrecise' shrinks the strides orbit by cardinality (unconditionally).
assumeSgtPreciseShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSgtPreciseShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeSgtPrecise w) a b)

-- | 'assumeSgePrecise' shrinks the strides orbit by cardinality (unconditionally).
assumeSgePreciseShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSgePreciseShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeSgePrecise w) a b)

-- | 'assumeNe' shrinks the strides orbit by cardinality (unconditionally):
-- 'S.assumeNe' only ever drops an endpoint, and 'S.reduce' shrinks further.
assumeNeShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeNeShrinks w a b =
  proper a ==> proper b ==> property (stridesShrinks (assumeNe w) a b)

-- | Shared body of the @assume*Shrinks@ properties: the result's strides
-- orbit is no larger than @a@'s. Uses the /O(1)/ 'S.size' of the strides
-- component, never the exponential joint 'size'\/'toList'. Returns 'Bool'
-- so it isn't mistaken for a standalone property.
stridesShrinks ::
  (Domain w -> Domain w -> Maybe (Domain w)) -> Domain w -> Domain w -> Bool
stridesShrinks op a b =
  case op a b of
    Nothing -> True
    Just c  -> S.size (strides c) <= S.size (strides a)

-- $assumeIdempotent
--
-- The @assume*Idempotent@ properties check that re-applying an assumption
-- denotes the same set, @assumeOp (assumeOp a b) b ≡ assumeOp a b@,
-- pointwise at a witness @x@ to avoid enumerating the (possibly
-- exponential) orbit. Idempotence is checked under the non-wrap guard,
-- where the underlying 'S.pseudoMeet' behaves as a lower bound.

-- | 'assumeSltPrecise' is idempotent (under the non-wrap guard).
assumeSltPreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
assumeSltPreciseIdempotent w a b x =
  proper a ==> proper b ==>
  Prelude.not (wraps a) ==> Prelude.not (wraps b) ==>
    property (idempotentAt (assumeSltPrecise w) a b x)

-- | 'assumeSlePrecise' is idempotent (under the non-wrap guard).
assumeSlePreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
assumeSlePreciseIdempotent w a b x =
  proper a ==> proper b ==>
  Prelude.not (wraps a) ==> Prelude.not (wraps b) ==>
    property (idempotentAt (assumeSlePrecise w) a b x)

-- | 'assumeSgtPrecise' is idempotent (under the non-wrap guard).
assumeSgtPreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
assumeSgtPreciseIdempotent w a b x =
  proper a ==> proper b ==>
  Prelude.not (wraps a) ==> Prelude.not (wraps b) ==>
    property (idempotentAt (assumeSgtPrecise w) a b x)

-- | 'assumeSgePrecise' is idempotent (under the non-wrap guard).
assumeSgePreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
assumeSgePreciseIdempotent w a b x =
  proper a ==> proper b ==>
  Prelude.not (wraps a) ==> Prelude.not (wraps b) ==>
    property (idempotentAt (assumeSgePrecise w) a b x)

-- | Shared body of the @assume*Idempotent@ properties (the @proper@\/
-- non-wrap guards live in each caller): @assumeOp _ b@ applied to
-- @assumeOp a b@ denotes the same set, checked pointwise at @x@. Returns
-- 'Bool' so it isn't mistaken for a standalone property.
idempotentAt ::
  (Domain w -> Domain w -> Maybe (Domain w)) ->
  Domain w -> Domain w -> Natural -> Bool
idempotentAt op a b x =
  case op a b of
    Nothing -> True
    Just c  -> maybeMember (op c b) x == member c x

-- | 'member' lifted through 'Maybe', but treating 'Nothing' as a failed
-- (rather than vacuously-true) soundness obligation: the @correct_assume*@
-- properties are conditioned on a witness @y@, so an empty result is a
-- genuine bug. Returns 'Bool' so it isn't mistaken for a standalone property.
maybeMemberOrFail :: Maybe (Domain w) -> Natural -> Bool
maybeMemberOrFail Nothing  _ = False
maybeMemberOrFail (Just c) x = member c x

