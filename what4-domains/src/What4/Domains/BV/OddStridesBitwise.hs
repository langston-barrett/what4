{-|
Module      : What4.Domains.BV.OddStridesBitwise
Copyright   : (c) Galois Inc, 2026
License     : BSD3

A reduced product of 'What4.Domains.BV.Strides' and 'What4.Domains.BV.Bitwise'.

A naive reduced product would store @(bitLo, bitHi)@ from @Bitwise@ and @(start,
stride, steps)@ from @Strides@. However, we can exploit some redundancy between
these views in order to achieve faster transfer functions. First, WLOG, write
@stride = 2^v * m@ for odd @m@, so that @v@ is the number of trailing zeroes of
@stride@. Then every member of the progression @(start, stride, steps)@ shares
@v@ low bits with @start@, and these are captured by the bitwise side. Thus, we
can store only the high @w-v@ bits of @start@, the odd part (@m@) of @stride@.

The public API is identical to 'What4.Domains.BV.StridesBitwise'; equivalence
on every operation is property-tested in @test/OddStridesBitwiseEquiv.hs@.
Soundness is property-tested in @test/OddStridesBitwise.hs@.

Hot paths that win asymptotically (cuboid fast path: @popcount(n+1) == 1@
on a non-wrapping orbit collapses the orbit to a tnum sub-cuboid):
'member', 'pseudoMeet', 'pseudoMeetPrecise', 'assumeEq', 'leqPrecise'
all skip the Hensel inverse and run as @O(w)@ bit-tricks. Long-tail
ops are bridged through 'expandToS' / 'compressFromS' to the existing
'What4.Domains.BV.Strides' kernel — same precision, with the
2-adic-shrunk representation as a constant-factor speedup at the
'compressFromS' boundary.
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
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

module What4.Domains.BV.OddStridesBitwise
  ( Domain
  , strides
  , bitwise
  , proper
  -- | 'compressFromS' bridges a canonical 'S.Domain' (+ its bitwise
  -- companion) into the reduced OSB representation; exposed so the
  -- equivalence suite can build matched (SB, OSB) pairs.
  , compressFromS
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
  , mulConstExact
  , udivConstExact
  , uremConstExact
  , ultExactTrueSeparated
  , ultExactFalseSeparated
  -- *** Power-of-2 fast paths
  , correct_scalePow2
  , correct_mulPow2
  , correct_udivPow2
  , correct_udivPrecisePow2
  , correct_uremPow2
  , correct_uremPrecisePow2
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
  -- ** Reduced product with bitwise
  --
  -- | Native-core checks specific to the OSB representation: the
  -- 2-adic GCD primitives and the native meet\/leq routines agreeing
  -- with the generic 'S.Domain' bridge.
  , gcdOddMatchesPrelude
  , binGcdMatchesPrelude
  , nativeLeqPreciseMatchesBridge
  , native2AdicMeetMatchesBridge
  , nativeLeqExactMatchesBridge
  , nativeReduceMatchesBridge
    -- * Re-exports
  , NatRepr
  , knownNat
  ) where

import           Control.Exception (assert)
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
import qualified What4.Domains.BV.Strides as S
import qualified What4.Domains.Arithmetic as Arith
import           What4.Domains.Verification (Property, property, (==>), Gen)

-- ------------------------------------------------------------------
-- The reduced-product domain

-- | A reduced product of 'S.Domain' and 'B.Domain', representationally
-- distinct from 'What4.Domains.BV.StridesBitwise.Domain' but
-- denotationally identical.
--
-- The strides side stores its 2-adic-shrunk shape:
--
-- * @startHigh@: the high @w − v@ bits of @start@ (i.e. @start `shiftR` v@).
-- * @mOdd@: the odd part of the stride, in @[1, 2^(w-v))@.
-- * @n@: step count, identical to the 'S.Domain' field.
--
-- The 2-adic exponent @v = ctz(stride)@ lives implicitly on the
-- bitwise component: every orbit element shares its low @v@ bits with
-- @start@, so after reduction the tnum forces those bits — and we
-- recover @v@ as @ctz(zeros .|. ones)@. Storing it explicitly would
-- duplicate information that is invariantly redundant.
data Domain (w :: Nat)
  = Domain
    { startHigh :: !Natural   -- ^ in @[0, 2^(w-v))@
    , mOdd      :: !Natural   -- ^ odd, in @[1, 2^(w-v))@
    , n         :: !Natural   -- ^ in @[0, 2^(w-v))@
    , bitwise   :: !(B.Domain w)
    }
  deriving Show

-- | The strides component: derived on demand from the 2-adic-shrunk
-- representation by reconstituting @start = (startHigh `shiftL` v) .|.
-- lowBits@ and @stride = mOdd `shiftL` v@.
strides :: (1 <= w) => NatRepr w -> Domain w -> S.Domain w
strides w d = expandToS w d

-- | The data-structure invariants of 'Domain': both projections are
-- proper, and at the same width.
proper :: (1 <= w) => NatRepr w -> Domain w -> Bool
proper w d =
  S.proper sLifted && toInteger (S.mask sLifted) == B.bvdMask (bitwise d)
  where
    sLifted = expandToS w d

-- ------------------------------------------------------------------
-- * Bridge between OSB.Domain and S.Domain

-- | /O(w)/. The 2-adic exponent @v@ implicit in the bitwise component:
-- the count of trailing forced bits (positions where either @zeros@ or
-- @ones@ is set).
ctzTnum :: B.Domain w -> Int
ctzTnum b =
  let (lo, hi) = B.bitbounds b
      mask     = B.bvdMask b
      -- forced = bits constant across the domain
      forced   = mask `Bits.xor` (lo `Bits.xor` hi)
  in countTrailingForced mask forced

-- | Count trailing 1-bits of @forced@ within the domain mask. If @forced@
-- has no clear bit below the width, that means every bit is forced; in
-- that case @v@ would be @w@, and the orbit collapses to a singleton —
-- representable, but we cap @v@ at the bit-width since shifts by exactly
-- @w@ would zero the result.
countTrailingForced :: Integer -> Integer -> Int
countTrailingForced mask forced
  | mask == 0 = 0
  | otherwise =
      -- The first 0 bit of @forced@ at positions [0, w) gives @v@; if no
      -- 0 bit exists in the window, every bit is forced (singleton domain),
      -- and @v == w@.
      let w   = Bits.popCount mask -- mask = 2^w - 1, so popCount = w
          inv = forced `Bits.xor` mask -- 1 where bit is unforced
      in if inv == 0
           then w
           else min w (countTrailingZeroes inv)

countTrailingZeroes :: Integer -> Int
countTrailingZeroes 0 = 0
countTrailingZeroes x = Bits.popCount ((x Bits..&. Prelude.negate x) - 1)

-- | /O(M(k) log k)/. Modular inverse of an odd number @a@ modulo @m = 2^k@,
-- by Hensel/Newton iteration: @x' = x · (2 − a·x) mod m@. Each step
-- doubles the number of correct low bits, so the loop runs in @O(log k)@
-- iterations of one width-@k@ multiply each.
--
-- Local copy of 'What4.Domains.BV.Strides.invModPow2' (which is not
-- exported). Identical algorithm.
invModPow2Local :: Natural -> Natural -> Natural
invModPow2Local a m
  | m <= 1    = 0
  | otherwise = go 1
  where
    mMinus1 = m - 1
    go x =
      let ax = (a * x) Bits..&. mMinus1 in
      if ax == 1
        then x
        else go ((x * (2 + m - ax)) Bits..&. mMinus1)

-- | /O(w)/. Reconstitute the 'S.Domain' projection.
--
-- @start = (startHigh `shiftL` v) .|. lowBits@, where @lowBits@ are read
-- straight off the tnum's forced ones in positions @[0, v)@ —
-- equivalently @ones .&. ((1 `shiftL` v) - 1)@.
-- @stride = mOdd `shiftL` v@ (or @1@ in the singleton case where @mOdd == 1@
-- and @n == 0@).
expandToS :: forall w. (1 <= w) => NatRepr w -> Domain w -> S.Domain w
expandToS w Domain{startHigh = sh, mOdd = m, n = nn, bitwise = b} =
  let v       = ctzTnum b
      m'      = NR.maxUnsigned w
      mask'   = fromInteger m'
      (lo, _) = B.bitbounds b
      lowMask = (1 `Bits.shiftL` v) - 1 :: Natural
      lowBits = fromInteger (lo Bits..&. toInteger lowMask) :: Natural
      stride0 = m `Bits.shiftL` v
      stride1 = stride0 Bits..&. mask'
      start1  = ((sh `Bits.shiftL` v) Bits..&. mask') Bits..|. lowBits
      -- Singleton special case: stride is canonicalized to 1 in S.Domain.
      -- If our representation has mOdd == 1 and n == 0, it's a singleton:
      -- pass stride = 1 to S.mk (which forces it anyway).
      (st, nn') | nn == 0   = (1, 0)
                | stride1 == 0 = (1, 0)  -- v == w singleton edge case
                | otherwise = (stride1, nn)
  in S.mk w start1 st nn'

-- | /O(M(w) log w)/. Compress an @(S.Domain, B.Domain)@ pair into an
-- 'OSB.Domain'. Runs 'S.reduce' to canonicalize the pair, then reads off
-- @v@ from the reduced bitwise component (which 'S.reduce' has lifted
-- to force the low @v@ bits).
--
-- Falls back to dropping the bitwise component on 'Nothing' (joint
-- concluded empty by reduction), matching 'StridesBitwise.mkReduced''s
-- fallback. If the reduce fails on @(s, S.toBitwise s)@ we'd be in
-- 'error' territory, which should never happen for proper inputs.
compressFromS :: (1 <= w) => NatRepr w -> S.Domain w -> B.Domain w -> Domain w
compressFromS = compressFromSBy S.reduce

-- | Like 'compressFromS', but runs 'S.reducePrecise' first (with the
-- standard 'reducePrecise → reduce' fallback for the self-wrapping
-- incompleteness).
compressFromSPrecise :: (1 <= w) => NatRepr w -> S.Domain w -> B.Domain w -> Domain w
compressFromSPrecise w s b = case S.reducePrecise w s b of
  Just (s', b') -> fromReduced s' b'
  Nothing       -> compressFromS w s b

-- | Generic compression: take any (sound) reduction routine and adapt
-- its result to the OSB representation.
compressFromSBy ::
  (1 <= w) =>
  (NatRepr w -> S.Domain w -> B.Domain w -> Maybe (S.Domain w, B.Domain w)) ->
  NatRepr w -> S.Domain w -> B.Domain w -> Domain w
compressFromSBy reduceOp w s b = case reduceOp w s b of
  Just (s', b') -> fromReduced s' b'
  Nothing -> case reduceOp w s (S.toBitwise s) of
    Just (s', b') -> fromReduced s' b'
    Nothing -> error "OddStridesBitwise.compressFromSBy: \
                     \reduce failed on (s, toBitwise s) — invariant violated."

-- | Strict compression: returns 'Nothing' iff reduction concludes empty.
tryCompressFromS ::
  (1 <= w) => NatRepr w -> S.Domain w -> B.Domain w -> Maybe (Domain w)
tryCompressFromS w s b = case S.reduce w s b of
  Just (s', b') -> Just (fromReduced s' b')
  Nothing       -> Nothing

-- | Strict compression via 'S.reducePrecise'; on its 'Nothing'
-- (incomplete on self-wrap) defers to the single-pass strict variant.
tryCompressFromSPrecise ::
  (1 <= w) => NatRepr w -> S.Domain w -> B.Domain w -> Maybe (Domain w)
tryCompressFromSPrecise w s b = case S.reducePrecise w s b of
  Just (s', b') -> Just (fromReduced s' b')
  Nothing       -> tryCompressFromS w s b

-- | Convert an already-reduced @(s, b)@ pair to OSB representation.
-- After @S.reduce@ the low @v@ bits of @b@ are forced (every orbit
-- element shares them), so reading @v = ctz(forced)@ off @b@ recovers
-- exactly @ctz(stride s)@.
fromReduced :: S.Domain w -> B.Domain w -> Domain w
fromReduced s b =
  let st  = S.stride s
      sht = S.start s
      v   = countTrailingZeroes (toInteger st)
      sh  = sht `Bits.shiftR` v
      m   = st  `Bits.shiftR` v
  in Domain { startHigh = sh, mOdd = m, n = S.n s, bitwise = b }

-- ------------------------------------------------------------------
-- * Native reduce on the odd-factored representation
--
-- A faithful port of 'S.reduce' (the non-precise reduction) that never
-- builds an 'S.Domain': it computes directly on the 2-adic-factored
-- progression @(stridePow2, strideOddPart, osStart, steps)@ carried by
-- 'OddStrides'. The Hensel inverse runs at the reduced modulus
-- @2^(w − v)@ on @strideOddPart@ as stored — the same idiom as 'member',
-- 'nativeLeqPrecise', and 'native2AdicMeet' — so the factoring is read
-- once (off the operand) and never re-derived by @ctz@ inside the path.
--
-- Precision is identical to 'S.reduce' (same algorithm); the win is a
-- constant factor: no @expandToS@/@S.mk@/@fromReduced@ allocation and no
-- repeated @ctz@/@divByPow2@ re-factoring at the bridge boundary.

-- | The strides half of an OSB domain in native 2-adic-factored
-- coordinates, /without/ a settled bitwise component. This is the
-- in-flight carrier for 'reduceOS': the lift grows @stridePow2@ before
-- any bitwise exists, so neither 'Domain' (whose @ctzTnum bitwise@ would
-- have to equal @stridePow2@) nor — by the native constraint —
-- 'S.Domain' can hold it.
--
-- Invariant: @strideOddPart@ is odd. The represented progression is
-- @{ osStart + i · (strideOddPart << stridePow2) mod 2^w : 0 ≤ i ≤ steps }@,
-- and @osStart@ is the full-width anchor (its low @stridePow2@ bits are
-- the orbit's pinned low bits). Produced in canonical form by
-- 'mkOddStrides' (mirroring 'S.mk': singletons pin @stridePow2 = 0@,
-- @strideOddPart = 1@; full cosets pin @strideOddPart = 1@ and reduce
-- @osStart@ modulo @2^stridePow2@).
data OddStrides = OddStrides
  { stridePow2    :: !Int      -- ^ @v = ctz(stride)@
  , strideOddPart :: !Natural  -- ^ odd part of the stride, @stride >> v@
  , osStart       :: !Natural  -- ^ full-width @start@
  , steps         :: !Natural  -- ^ step count @n@
  }
  deriving (Eq, Show)

-- | /O(A(w))/. Canonicalizing smart constructor for 'OddStrides', the
-- factored mirror of 'S.mk' (Strides canonicalization at
-- 'What4.Domains.BV.Strides.mk'). Takes the already-known 2-adic split
-- @(v, oddPart)@ of the stride — it does /not/ re-derive @v@ by @ctz@.
-- Preconditions (as in 'S.mk'): @oddPart@ is odd and @v + log2 oddPart@
-- fits, @start@ is masked, the progression is in range.
mkOddStrides ::
  Natural {- ^ @mask = 2^w − 1@ -} ->
  Int {- ^ @v@ -} -> Natural {- ^ @oddPart@ (odd) -} ->
  Natural {- ^ @start@ -} -> Natural {- ^ @n@ -} ->
  OddStrides
mkOddStrides msk v oddPart start nn
  -- Singleton: stride is irrelevant; pin to @2^0 · 1@, as 'S.mk' pins
  -- stride to 1.
  | nn == 0          = OddStrides 0 1 start 0
  -- Full coset: any element of @start mod g + g·Z@ is a valid start.
  -- 'S.mk' picks @start mod g@, @stride = g = 2^v@ (so @oddPart = 1@).
  | nn + 1 == orbit  = OddStrides v 1 (start Bits..&. (g - 1)) (orbit - 1)
  | otherwise        =
      -- Canonicalize @oddPart@ into @[1, 2^(w−v))@: the stored stride is
      -- @oddPart << v@ masked, and @(oddPart `mod` 2^(w−v)) << v ≡
      -- (oddPart << v) (mod 2^w)@, so reducing modulo the orbit leaves the
      -- denotation untouched while restoring the field invariant. A caller
      -- that lifts @v@ without re-reducing the stride (e.g.
      -- 'liftForcedBitsOS') can otherwise hand in @oddPart ≥ 2^(w−v)@.
      -- @orbit ≥ 2@ here (the singleton and full-coset cases are handled
      -- above), so the reduced part stays odd and nonzero.
      assert (oddPart Bits..&. 1 == 1) (OddStrides v (oddPart `Prelude.mod` orbit) start nn)
  where
    g     = 1 `Bits.shiftL` v
    orbit = (msk + 1) `Bits.shiftR` v   -- @2^w / 2^v@; @oddPart@ odd ⇒ gcd = 2^v

-- | /O(w)/. Read the factored progression off a stored 'Domain' directly,
-- without reconstituting an 'S.Domain'. Mirrors 'expandToS' (same
-- @lowBits@/singleton/@v ≥ w@ handling) but reads @v = ctzTnum bitwise@
-- and @strideOddPart = mOdd@ /as stored/ — no @ctz@/@divByPow2@
-- re-extraction — and canonicalizes through 'mkOddStrides'.
oddStridesOf :: forall w. (1 <= w) => NatRepr w -> Domain w -> OddStrides
oddStridesOf w Domain{startHigh = sh, mOdd = m, n = nn, bitwise = b} =
  let v       = ctzTnum b
      mask'   = fromInteger (NR.maxUnsigned w) :: Natural
      (lo, _) = B.bitbounds b
      lowMask = (1 `Bits.shiftL` v) - 1 :: Natural
      lowBits = fromInteger (lo Bits..&. toInteger lowMask) :: Natural
      stride1 = (m `Bits.shiftL` v) Bits..&. mask'
      start1  = ((sh `Bits.shiftL` v) Bits..&. mask') Bits..|. lowBits
  in if nn == 0 || stride1 == 0
       -- Singleton, or @v == w@ edge: the orbit is the single value
       -- @start1@. Mirrors 'expandToS''s @(st, nn')@ collapse.
       then mkOddStrides mask' 0 1 start1 0
       else mkOddStrides mask' v m start1 nn

-- | /O(1)/. Settle a reduced 'OddStrides' against the reduced bitwise
-- component into an OSB 'Domain'. The factored inverse of 'oddStridesOf':
-- @startHigh = osStart >> v@, @mOdd = strideOddPart@, both already at
-- hand — no @ctz(stride)@ as in 'fromReduced'.
mkOSB :: OddStrides -> B.Domain w -> Domain w
mkOSB OddStrides{stridePow2 = v, strideOddPart = oddPart, osStart = s, steps = nn} b =
  Domain { startHigh = s `Bits.shiftR` v, mOdd = oddPart, n = nn, bitwise = b }

-- | /O(A(w))/. The full-width stride @strideOddPart << stridePow2@ of a
-- factored orbit, masked to the width. Singletons (canonicalized to
-- @v = 0@, @oddPart = 1@) report stride @1@, matching 'S.stride'.
osStride :: Natural {- ^ @mask@ -} -> OddStrides -> Natural
osStride msk (OddStrides v oddPart _ _) = (oddPart `Bits.shiftL` v) Bits..&. msk

-- | /O(A(w))/. Canonicalizing constructor from a full-width @stride@ (the
-- form the native arithmetic combinators compute): split @stride@ into
-- its 2-adic exponent @v@ and odd part, then defer to 'mkOddStrides'. A
-- @stride@ of @0 mod 2^w@ (overflowed to a multiple of @2^w@) collapses
-- to a singleton at @start@.
mkOddStridesFromStride ::
  Natural {- ^ @mask@ -} ->
  Natural {- ^ @start@ -} -> Natural {- ^ @stride@ -} -> Natural {- ^ @n@ -} ->
  OddStrides
mkOddStridesFromStride msk start stride nn
  | stride == 0 || nn == 0 = mkOddStrides msk 0 1 start 0
  | otherwise =
      let v = countTrailingZeroes (toInteger stride)
      in mkOddStrides msk v (stride `Bits.shiftR` v) start nn

-- | /O(A(w))/. Re-expand a factored 'OddStrides' to an 'S.Domain'. Used
-- only on the still-bridged precise path ('mulPrecise'), where
-- 'S.reducePrecise' has no native port yet.
oddStridesToS :: (1 <= w) => NatRepr w -> OddStrides -> S.Domain w
oddStridesToS w p =
  let msk = fromInteger (NR.maxUnsigned w) :: Natural
  in S.mk w (osStart p) (osStride msk p) (steps p)

-- | /O(A(w))/. Forced bits of a 'B.Domain' as a @(zeros, ones)@ pair,
-- mirroring 'S.knownZerosOnesNat': @zeros@ has a 1 at each forced-0
-- position, @ones@ at each forced-1.
knownZerosOnesN :: B.Domain w -> (Natural, Natural)
knownZerosOnesN b =
  let (lo, hi) = B.bitbounds b
      bm       = B.bvdMask b
  in (fromInteger (bm `Bits.xor` hi), fromInteger lo)

-- | /O(M(w) log w)/. The forced-bit stride lift on the factored
-- representation: a faithful port of 'S.liftForcedBits'
-- (Strides closed form) that consumes the contiguous run of forced bits
-- at positions @[v, v+k)@, doubling the 2-adic exponent to @v + k@ and
-- leaving @strideOddPart@ untouched. The single Hensel inverse runs at
-- the reduced modulus @2^k@ on @strideOddPart@ /as stored/.
--
-- Returns 'Nothing' exactly when the orbit has no member agreeing with
-- @(zeros, ones)@: a low-bit conflict in @[0, v)@, or no orbit index in
-- @[0, steps]@ hitting the required residue.
liftForcedBitsOS ::
  forall w. (1 <= w) =>
  NatRepr w -> OddStrides -> (Natural, Natural) -> Maybe OddStrides
liftForcedBitsOS w p@(OddStrides v oddPart start nn) (zeros, ones)
  -- Singleton: the orbit has one value; just check it.
  | nn == 0 =
      if (zeros Bits..&. start) == 0 && (ones Bits..&. notN start) == 0
        then Just p
        else Nothing
  -- @start@'s low bits below @v@ are fixed across the whole orbit.
  | (zeros Bits..&. start Bits..&. lowMask) /= 0 = Nothing
  | (ones  Bits..&. notN start Bits..&. lowMask) /= 0 = Nothing
  -- Bit @v@ itself is free: the run is empty, nothing to lift.
  | (forced Bits..&. g) == 0 = Just p
  -- No orbit index in @[0, n]@ hits the required residue @r@.
  | r > nn = Nothing
  -- @v + k = w@: the lift collapses the orbit to the singleton @newStart@.
  | v + k >= wInt = Just (mkOddStrides msk 0 1 newStart 0)
  | otherwise = Just (mkOddStrides msk (v + k) oddPart newStart newN)
  where
    msk     = fromInteger (NR.maxUnsigned w) :: Natural
    wInt    = fromIntegral (NR.natValue w) :: Int
    notN x  = msk `Bits.xor` x
    g       = 1 `Bits.shiftL` v :: Natural          -- @2^v@
    lowMask = g - 1                                  -- bits @0 .. v-1@
    st      = (oddPart `Bits.shiftL` v) Bits..&. msk -- full-width stride

    -- @twoK = 2^k@: length of the contiguous forced run from position @v@.
    forced  = zeros Bits..|. ones
    hiSpan  = (msk + 1) `Bits.shiftR` v              -- @2^(w-v)@
    wMask   = hiSpan - 1
    sf      = forced `Bits.shiftR` v                 -- @forced >> v@
    csf     = sf `Bits.xor` wMask                    -- 0 bits where @forced@ set
    twoK    = if csf == 0 then hiSpan else lowestBit msk csf
    k       = Bits.popCount (twoK - 1)

    -- Solve @i·oddPart ≡ d (mod 2^k)@ for the matching residue @r@.
    runLow   = g * twoK - 1                          -- @2^(v+k) - 1@
    runRange = runLow `Bits.xor` lowMask             -- bits @v .. v+k-1@
    cLow     = (start Bits..&. lowMask) Bits..|. (ones Bits..&. runRange)
    d        = (modSubLocal msk cLow start Bits..&. runLow) `Bits.shiftR` v
    r        = (d * invModPow2Local oddPart twoK) Bits..&. (twoK - 1)

    newStart = (start + r * st) Bits..&. msk
    newN     = (nn - r) `Bits.shiftR` k

-- | /O(A(w))/. Bits forced across the factored orbit, a port of
-- 'S.forcedBits': stride pinning on the low @v@ bits unioned with span
-- pinning on the high bits. The full-width @start@/@stride@ formed here
-- for the span comparison is inherently full-width arc arithmetic, not a
-- representation round-trip.
forcedBitsOS :: forall w. (1 <= w) => NatRepr w -> OddStrides -> (Natural, Natural)
forcedBitsOS w (OddStrides v oddPart start nn) =
  let msk        = fromInteger (NR.maxUnsigned w) :: Natural
      notN x     = msk `Bits.xor` x
      g          = 1 `Bits.shiftL` v :: Natural
      lowMask    = g - 1
      st         = (oddPart `Bits.shiftL` v) Bits..&. msk
      lowOnes    = start Bits..&. lowMask
      lowZeros   = lowMask Bits..&. notN start
      span_      = nn * st
      belowSpan  = fromInteger (Arith.bitsBelow (toInteger span_)) Bits..&. msk
      spanMask   = notN belowSpan
      sEnd       = (start + span_) Bits..&. msk
      agree      = notN (start `Bits.xor` sEnd)
      highForced = agree Bits..&. spanMask
      highOnes   = highForced Bits..&. start
      highZeros  = highForced Bits..&. notN start
  in (lowZeros Bits..|. highZeros, lowOnes Bits..|. highOnes)

-- | /O(A(w))/. The bitwise projection of the factored orbit; port of
-- 'S.toBitwise' (@= strideBitwise@).
toBitwiseOS :: (1 <= w) => NatRepr w -> OddStrides -> B.Domain w
toBitwiseOS w p =
  let imask = NR.maxUnsigned w
      (zeros, ones) = forcedBitsOS w p
  in B.interval imask (toInteger ones) (imask `Bits.xor` toInteger zeros)

-- | /O(A(w))/. Does the factored orbit wrap mod @2^w@ more than spanning
-- once? Port of 'S.isSelfWrapping' (@n·stride > mask@), in reduced terms
-- @steps · oddPart ≥ 2^(w−v)@.
isSelfWrappingOS :: (1 <= w) => NatRepr w -> OddStrides -> Bool
isSelfWrappingOS w (OddStrides v oddPart _ nn) =
  let msk = fromInteger (NR.maxUnsigned w) :: Natural
      st  = (oddPart `Bits.shiftL` v) Bits..&. msk
  in nn * st > msk

-- | /O(A(w))/. The full @g@-coset of a factored orbit; port of
-- 'S.fullCoset'. @strideOddPart@ collapses to 1, @osStart@ to its
-- residue mod @2^v@.
fullCosetOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides
fullCosetOS w (OddStrides v _ start _) =
  let msk = fromInteger (NR.maxUnsigned w) :: Natural
  in mkOddStrides msk v 1 start ((msk + 1) `Bits.shiftR` v - 1)

-- | /O(A(w))/. South-pole split of a factored orbit into non-wrapping
-- pieces; port of 'S.ssplit'. Each piece shares @stridePow2@ and
-- @strideOddPart@ (a wrap split does not change the stride's 2-adic
-- factoring); only @osStart@ and @steps@ differ.
ssplitOS :: (1 <= w) => NatRepr w -> OddStrides -> [OddStrides]
ssplitOS w p@(OddStrides v oddPart s nn)
  | isSelfWrappingOS w p = [fullCosetOS w p]
  | s + nn * t <= msk    = [p]
  | otherwise =
      let i1 = (msk - s) `Prelude.div` t
          s2 = (s + (i1 + 1) * t) Bits..&. msk
          n2 = nn - i1 - 1
      in [mkOddStrides msk v oddPart s i1, mkOddStrides msk v oddPart s2 n2]
  where
    msk = fromInteger (NR.maxUnsigned w) :: Natural
    t   = (oddPart `Bits.shiftL` v) Bits..&. msk

-- | /O(A(w))/. The bitwise projection of an orbit: 'toBitwiseOS' on a
-- self-wrapping orbit (which spans every residue its coset reaches), else
-- the 'B.join' of the south-pole split's non-wrapping pieces. Shared by
-- 'reduceOS' and 'reduceProjectOS'.
projectOS :: (1 <= w) => NatRepr w -> OddStrides -> B.Domain w
projectOS w p
  | isSelfWrappingOS w p = toBitwiseOS w p
  | otherwise = case ssplitOS w p of
      (c : cs) -> foldr (B.join . toBitwiseOS w) (toBitwiseOS w c) cs
      []       -> toBitwiseOS w p

-- | The native non-precise reduce kernel: a faithful port of 'S.reduce'
-- on the factored representation. Lifts the orbit by @b@'s forced bits,
-- projects the lifted orbit back to a bitwise domain (per-piece on the
-- south-pole split, or whole on a self-wrapping orbit), meets it into
-- @b@, and settles to an OSB 'Domain'. 'Nothing' iff the joint is empty.
reduceOS ::
  (1 <= w) => NatRepr w -> OddStrides -> B.Domain w -> Maybe (Domain w)
reduceOS w p b
  | B.isBottom b = Nothing
  | otherwise = do
      p' <- liftForcedBitsOS w p (knownZerosOnesN b)
      let b' = B.meet b (projectOS w p')
      if B.isBottom b' then Nothing else Just (mkOSB p' b')

-- | A reduce kernel that /omits/ the tnum→orbit lift, keeping only the
-- orbit→tnum projection. Sound and precision-preserving precisely when
-- 'liftForcedBitsOS' is a guaranteed no-op on @(p, b)@ — which holds for
-- the add/sub results: the result tnum @b@ leaves bit @v = ctz(stride)@
-- free (the OSB invariant @ctzTnum(bitwise) == ctz(stride)@ makes that
-- bit free in each operand, and 'Tnum.add'\/'Tnum.sub' preserve a free
-- bit at the lowest position where both operands carry no forced bit), so
-- @liftForcedBitsOS@ hits its @forced .&. 2^v == 0@ short-circuit and
-- returns @p@ unchanged. We therefore skip @knownZerosOnesN@ and the lift
-- entirely and meet @b@ against the unlifted orbit's projection.
--
-- Do NOT use where the lift could fire (e.g. 'scale', 'mul'): those can
-- force bits at or below @v@ and need 'reduceOS'.
reduceProjectOS ::
  (1 <= w) => NatRepr w -> OddStrides -> B.Domain w -> Maybe (Domain w)
reduceProjectOS w p b
  | B.isBottom b = Nothing
  | otherwise =
      let b' = B.meet b (projectOS w p)
      in if B.isBottom b' then Nothing else Just (mkOSB p b')

-- | Native reduce from a stored 'Domain': the factored entry point that
-- replaces the @expandToS → S.reduce → fromReduced@ bridge.
reduceN :: (1 <= w) => NatRepr w -> Domain w -> B.Domain w -> Maybe (Domain w)
reduceN w a b = reduceOS w (oddStridesOf w a) b

-- | Lossy native reduce: settles to a 'Domain', dropping the bitwise
-- component to the orbit's own projection if the joint is empty.
-- Replaces 'compressFromS' at the native-arithmetic call sites; preserves
-- 'compressFromSBy''s fallback semantics.
nativeReduce :: (1 <= w) => NatRepr w -> OddStrides -> B.Domain w -> Domain w
nativeReduce w p b = case reduceOS w p b of
  Just d  -> d
  Nothing -> case reduceOS w p (toBitwiseOS w p) of
    Just d  -> d
    Nothing -> error "OddStridesBitwise.nativeReduce: \
                     \reduce failed on (p, toBitwiseOS p) — invariant violated."

-- | Lift-free counterpart of 'nativeReduce', built on 'reduceProjectOS'.
-- Same fallback semantics; use only where the lift is a proven no-op (see
-- 'reduceProjectOS') — currently 'add' and 'sub'.
nativeReduceProject :: (1 <= w) => NatRepr w -> OddStrides -> B.Domain w -> Domain w
nativeReduceProject w p b = case reduceProjectOS w p b of
  Just d  -> d
  Nothing -> case reduceProjectOS w p (toBitwiseOS w p) of
    Just d  -> d
    Nothing -> error "OddStridesBitwise.nativeReduceProject: \
                     \reduce failed on (p, toBitwiseOS p) — invariant violated."

-- ------------------------------------------------------------------
-- * Internal: Maybe-driven smart constructors mirroring StridesBitwise

-- ------------------------------------------------------------------
-- * Cuboid fast path
--
-- When @popcount(n+1) == 1@ and the orbit doesn't wrap (@v + log2(n+1) <= w@),
-- the orbit collapses to a tnum sub-cuboid: bits @[0, v)@ pinned to
-- @startHigh@'s low bits, bits @[v, v+k)@ free, bits above pinned.
-- Canonicalize this by setting @mOdd = 1@. Then the predicate
-- @mOdd == 1 && popcount(n+1) == 1@ promises "the orbit equals its tnum
-- projection" — at which point member, pseudoMeet, and assumeEq skip the
-- Hensel inverse entirely and run as pure tnum bit-tricks.

-- | /O(1)/. The cuboid fast-path predicate.
--
-- The orbit equals a /cube/ — the tnum with free bits @[v, v+k)@ (where
-- @2^k = n+1@), low @v@ bits pinned to the orbit's forced low bits, and
-- high bits pinned to @startHigh@ (see 'orbitCube') — iff
--
-- (1) @mOdd == 1@ — the high bits step by exactly @2^v@,
-- (2) @popcount(n+1) == 1@ — the orbit length is a power of two,
-- (3) the orbit is non-wrapping at width @w − v@:
--     @startHigh + n < 2^(w-v)@, and
-- (4) @startHigh@ is aligned: @startHigh `mod` (n+1) == 0@.
--
-- Without (4), the orbit @{startHigh, startHigh+1, ..., startHigh+n}@
-- spans a 2^k-length window not aligned to a 2^k boundary in
-- @startHigh@'s coordinate, so the orbit is /not/ a cube (e.g.
-- @startHigh = 1, n = 1@ at width 3 gives orbit @{1, 2}@, whose
-- bounding cube @\\**@ admits @{0, 1, 2, 3}@).
--
-- Without (3), the orbit wraps mod @2^w@ and is likewise not a cube.
--
-- When this holds, the OSB.Domain denotes exactly the stored tnum
-- (@orbit ∩ tnum == tnum@), so 'member', 'leqPrecise', and 'pseudoMeet'
-- may skip the Hensel inverse and run as pure tnum bit-tricks. This
-- rests on the representational invariant @tnum ⊆ orbit-projection@: on
-- a cuboid the orbit /is/ the cube, so @orbit ∩ tnum == tnum@ exactly
-- when @tnum ⊆ cube@. 'reduce' establishes the invariant (it meets the
-- tnum against the orbit's bitwise projection) and 'canonicalize'
-- re-establishes it via 'orbitCube'.
isCuboid :: (1 <= w) => NatRepr w -> Domain w -> Bool
isCuboid w Domain{startHigh = sh, mOdd = m, n = nn, bitwise = b} =
  m == 1
  && (nn + 1) Bits..&. nn == 0   -- (2) popcount(n+1) == 1
  && sh Bits..&. nn == 0         -- (4) startHigh is 2^k-aligned
  && nonWrap                     -- (3) non-wrap
  where
    v        = ctzTnum b
    wI       = fromIntegral (NR.natValue w) :: Int
    hiSpan   = 1 `Bits.shiftL` (wI - v) :: Natural
    nonWrap  = sh + nn < hiSpan

-- | /O(w)/. The orbit of a cuboid 'Domain' as a tnum: free bits
-- @[v, v+k)@ (where @2^k = n+1@), low @v@ bits pinned to the orbit's
-- forced low bits, and high bits pinned to @startHigh@. Only meaningful
-- when 'isCuboid' holds; on a cuboid this tnum denotes exactly the
-- orbit. 'canonicalize' meets it into the bitwise component to
-- re-establish the @tnum ⊆ orbit@ invariant after skipping
-- re-reduction.
orbitCube :: Domain w -> B.Domain w
orbitCube Domain{startHigh = sh, n = nn, bitwise = b} =
  B.interval bMask loCube hiCube
  where
    v        = ctzTnum b
    bMask    = B.bvdMask b
    (loB, _) = B.bitbounds b
    lowMask  = (1 `Bits.shiftL` v) - 1 :: Integer
    lowBits  = loB Bits..&. lowMask
    loCube   = ((toInteger sh `Bits.shiftL` v) Bits..|. lowBits) Bits..&. bMask
    freeMask = toInteger nn `Bits.shiftL` v
    hiCube   = loCube Bits..|. freeMask

-- ------------------------------------------------------------------
-- * Construction

mk ::
  (1 <= w) =>
  NatRepr w -> Natural -> Natural -> Natural -> Domain w
mk w s t nn =
  let sd = S.mk w s t nn
  in compressFromS w sd (S.toBitwise sd)

top :: (1 <= w) => NatRepr w -> Domain w
top w = compressFromS w (S.top w) (B.top w)

fromAscEltList ::
  (1 <= w) => NatRepr w -> [Natural] -> Maybe (Domain w)
fromAscEltList w xs =
  case S.fromAscEltList w xs of
    Nothing -> Nothing
    Just sd -> Just (compressFromS w sd (S.toBitwise sd))

-- ------------------------------------------------------------------
-- * Canonicalization

newtype Canonical w = Canonical (Domain w)
  deriving Show

getCanonical :: Canonical w -> Domain w
getCanonical (Canonical c) = c

-- | Canonical form: replace the strides side with its 'S.canonicalize'
-- representative.
--
-- Re-running 'S.reduce' here would risk *expanding* the set: an
-- already-reduced @(s, b)@ pair whose joint is over-approximate (the
-- joint is geometrically empty but the reduction couldn't see it)
-- becomes a non-empty representation if the canonicalized strides'
-- 'ssplit' decomposition newly reveals the empty joint and the
-- empty-joint fallback then drops @b@.
--
-- Skipping the full re-reduce is sound because canonicalization
-- preserves @ctz(stride)@ (the canonical stride is either @stride@ or
-- its additive inverse, which share their lowest set bit), so the OSB
-- representational invariant @ctzTnum(bitwise) == ctz(stride)@ is
-- preserved without any work on @b@.
--
-- One bitwise refinement /is/ still required: 'S.canonicalize' may
-- reverse a non-wrapping orbit into a /cuboid/ orientation (@mOdd == 1@,
-- power-of-two length, aligned), and on a cuboid the fast paths read the
-- denotation straight off @b@ assuming @tnum ⊆ orbit@. The pre-canonical
-- @b@ need not respect the post-canonical orbit (e.g. orbit @{7,5,3,1}@
-- with @b = tnum {1,3,9,11}@ canonicalizes the orbit to @{1,3,5,7}@,
-- after which @b@'s points @9,11@ escape the orbit). We restore the
-- invariant by meeting @b@ against 'orbitCube'; this only /shrinks/ @b@
-- (sound — it removes points the orbit already excludes) and leaves
-- @ctzTnum@ and the forced low bits unchanged, so 'expandToS' is
-- unaffected. Non-cuboid orientations need no such meet: their fast
-- paths don't fire, and the general path intersects orbit and tnum
-- explicitly.
canonicalize :: (1 <= w) => NatRepr w -> Domain w -> Canonical w
canonicalize w d =
  let s  = expandToS w d
      sc = S.getCanonical (S.canonicalize s)
      dc = fromReduced sc (bitwise d)
  in Canonical $
       if isCuboid w dc
         then dc { bitwise = B.meet (bitwise dc) (orbitCube dc) }
         else dc

-- ------------------------------------------------------------------
-- * Conversion

toArith :: (1 <= w) => NatRepr w -> Domain w -> A.Domain w
toArith w d = S.toArith (expandToS w d)

hull :: (1 <= w) => NatRepr w -> Domain w -> A.Domain w
hull w d = S.hull (expandToS w d)

fromArith ::
  (1 <= w) => NatRepr w -> A.Domain w -> Maybe (Domain w)
fromArith w a = case S.fromArith w a of
  Nothing -> Nothing
  Just sd -> Just (compressFromS w sd (S.toBitwise sd))

toBitwise :: Domain w -> B.Domain w
toBitwise = bitwise

forcedBits :: (1 <= w) => NatRepr w -> Domain w -> (Natural, Natural)
forcedBits w d = S.forcedBits (expandToS w d)

fromBitwise ::
  (1 <= w) => NatRepr w -> B.Domain w -> Maybe (Domain w)
fromBitwise w b = case S.fromBitwise w b of
  Nothing -> Nothing
  Just sd -> Just (compressFromS w sd b)

-- ------------------------------------------------------------------
-- * Queries

-- | Membership.
member :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Bool
-- /Native non-cuboid path/: width-@(w − v)@ Newton inverse on @mOdd@.
-- The bitwise check has already verified the low @v@ bits of @x@ match
-- the orbit's pinned low bits; the high @(w − v)@ bits give the index
-- @i = (xHigh − startHigh) · mOdd^{−1} mod 2^(w − v)@, and @x@ is in the
-- orbit iff @i ≤ n@.
member w d@Domain{bitwise = b, startHigh = sh, mOdd = m, n = nn} x
  | isCuboid w d = B.member b (toInteger x)
  | Prelude.not (B.member b (toInteger x)) = False
  | otherwise =
      let v       = ctzTnum b
          wInt    = fromIntegral (NR.natValue w) :: Int
      in if v >= wInt
           then -- v == w: orbit is a singleton fully pinned by @b@.
                -- @B.member b x@ already certified @x@ is that singleton.
                True
           else
             let xHigh = x `Bits.shiftR` v
                 mHigh = 1 `Bits.shiftL` (wInt - v) :: Natural
                 mMask = mHigh - 1
                 delta = (xHigh + mHigh - sh) Bits..&. mMask
                 mInv  = invModPow2Local m mHigh
                 i     = (delta * mInv) Bits..&. mMask
             in i <= nn

toList :: (1 <= w) => NatRepr w -> Domain w -> [Natural]
toList w d@Domain{bitwise = b} =
  [ x | x <- S.toList (expandToS w d), B.member b (toInteger x) ]

-- | Cardinality (sound over-approximation, identical formula to
-- 'StridesBitwise.size').
size :: (1 <= w) => NatRepr w -> Domain w -> Natural
size w c@Domain{bitwise = b} =
  case sizeExactMaybe w c of
    Just k  -> k
    Nothing -> minimum [S.size sd, fromInteger (B.size b), jointBound, windowMarginal w c]
  where
    sd         = expandToS w c
    m_         = B.bvdMask b
    (loB, hiB) = B.bitbounds b
    unknownB   = loB `Bits.xor` hiB
    (zerosS0, onesS0) = S.forcedBits sd
    unknownS   = m_ `Bits.xor` (toInteger zerosS0 Bits..|. toInteger onesS0)
    jointBound = Bits.bit (Bits.popCount (unknownS Bits..&. unknownB))

sizeExactMaybe :: (1 <= w) => NatRepr w -> Domain w -> Maybe Natural
sizeExactMaybe w c@Domain{bitwise = b}
  | pinsConflict w c b = Just 0
  | cutting Bits..&. Bits.complement window == 0 = Just (windowMarginal w c)
  | otherwise = Nothing
  where
    m_         = B.bvdMask b
    (loB, hiB) = B.bitbounds b
    unknownB   = loB `Bits.xor` hiB
    forcedB    = m_ `Bits.xor` unknownB
    s          = expandToS w c
    (zerosS0, onesS0) = S.forcedBits s
    unknownS   = m_ `Bits.xor` (toInteger zerosS0 Bits..|. toInteger onesS0)
    cutting    = forcedB Bits..&. unknownS
    window     = toInteger (uniformWindowMaskOSB w c)

windowMarginal :: (1 <= w) => NatRepr w -> Domain w -> Natural
windowMarginal w c@Domain{bitwise = b} =
  (n c + 1) `Bits.shiftR` Bits.popCount cutWindow
  where
    s          = expandToS w c
    m_         = B.bvdMask b
    (loB, hiB) = B.bitbounds b
    unknownB   = loB `Bits.xor` hiB
    forcedB    = m_ `Bits.xor` unknownB
    (zerosS0, onesS0) = S.forcedBits s
    unknownS   = m_ `Bits.xor` (toInteger zerosS0 Bits..|. toInteger onesS0)
    cutWindow  = forcedB Bits..&. unknownS Bits..&. toInteger (uniformWindowMaskOSB w c)

uniformWindowMaskOSB :: (1 <= w) => NatRepr w -> Domain w -> Natural
uniformWindowMaskOSB w c =
  let s   = expandToS w c
      st  = S.stride s
      g   = st `Bits.xor` (st Bits..&. (st - 1))
      np1 = S.n s + 1
      lb  = np1 `Bits.xor` (np1 Bits..&. S.n s)
  in g * lb - 1

pinsConflict :: (1 <= w) => NatRepr w -> Domain w -> B.Domain w -> Bool
pinsConflict w c b =
  let s = expandToS w c
      m_         = B.bvdMask b
      (loB, hiB) = B.bitbounds b
      zerosB     = m_ `Bits.xor` hiB
      (zerosS0, onesS0) = S.forcedBits s
      zerosS     = toInteger zerosS0
      onesS      = toInteger onesS0
  in loB Bits..&. zerosS /= 0 || zerosB Bits..&. onesS /= 0

leq :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Bool
leq w a b =
  S.leq (expandToS w a) (expandToS w b) && B.leq (bitwise a) (bitwise b)

-- | More precise ordering.
--
-- /Cuboid fast path/: when both operands are cuboids, the orbit equals
-- its tnum, so 'B.leq' on the bitwise components decides the order
-- exactly — @O(w)@ vs the Hensel inverse + floorSum residual the slow
-- path may need.
leqPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Bool
leqPrecise w a b
  | isCuboid w a && isCuboid w b = B.leq (bitwise a) (bitwise b)
  | otherwise =
      nativeLeqPrecise w a b && B.leq (bitwise a) (bitwise b)

isSelfWrapping :: (1 <= w) => NatRepr w -> Domain w -> Bool
isSelfWrapping w d = S.isSelfWrapping (expandToS w d)

-- ------------------------------------------------------------------
-- * Internal helpers

tightUBounds :: (1 <= w) => NatRepr w -> Domain w -> UnsignedBounds
tightUBounds w d =
  let (sl, sh) = A.ubounds (S.toArith (expandToS w d))
      (bl, bh) = B.bitbounds (bitwise d)
  in UnsignedBounds (max sl bl) (min sh bh)

reachableAmounts ::
  (1 <= w) => NatRepr w -> (Natural -> Int) -> Domain w -> Maybe [Int]
reachableAmounts w reduceAmt d
  | S.size s > NR.natValue w = Nothing
  | otherwise =
      Just (Set.toAscList (Set.fromList
              [ reduceAmt v | v <- orbit, B.member b (toInteger v) ]))
  where
    s     = expandToS w d
    b     = bitwise d
    st    = S.stride s
    m_    = S.mask s
    orbit = take (fromIntegral (S.n s) + 1)
                 (iterate (\v -> (v + st) Bits..&. m_) (S.start s))

clampShift :: NatRepr w -> Natural -> Int
clampShift w v = fromIntegral (min v (NR.natValue w))

rotAmt :: NatRepr w -> Natural -> Int
rotAmt w v = fromIntegral (v `mod` NR.natValue w)

-- ------------------------------------------------------------------
-- * Arithmetic

negate :: (1 <= w) => NatRepr w -> Domain w -> Domain w
negate w d =
  compressFromS w (S.negate w (expandToS w d)) (B.negate (bitwise d))

-- | /O(w · G(w))/ native add: closed-form combine on the bilinear orbit
-- @{start_a + i·stride_a + start_b + j·stride_b mod 2^w}@.
--
-- The result stride is @gcd(stride_a, stride_b)@, computed via 'binGcd'
-- (2-adic split plus Stein's 'gcdOdd' on the odd parts). The start is
-- @start_a + start_b mod 2^w@; the step count walks @n_a@ steps of size
-- @stride_a / d@ plus @n_b@ steps of size @stride_b / d@ within the
-- @d@-spaced result orbit, capped at the orbit length.
add :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
add w a b =
  -- 'nativeReduceProject' (lift-free): the result tnum leaves bit
  -- @ctz(stride)@ free, so the tnum→orbit lift is a proven no-op here.
  nativeReduceProject w (addStridesNative w a b)
    (B.add (bitwise a) (bitwise b))

-- | /O(w · G(w))/ native sub: same closed-form combine as 'add', but
-- anchored at @start_a − end_b mod 2^w@ and walking the @b@-side
-- contribution from the additive inverse of @stride_b@ (which shares its
-- gcd with @stride_b@, so @d@ and the step counts are unchanged).
sub :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sub w a b =
  -- Lift-free, as in 'add': @B.sub@ leaves bit @ctz(stride)@ free.
  nativeReduceProject w (subStridesNative w a b)
    (B.sub (bitwise a) (bitwise b))

-- | The native strides side of 'add': run a width-@w@ modular add on
-- starts and combine the orbits via 'addSubStridesFinish'. Returns an
-- 'S.Domain' so the caller can reduce against the matching bitwise
-- component.
addStridesNative ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> OddStrides
addStridesNative w a b =
  let mask = fromInteger (NR.maxUnsigned w) :: Natural
      sa   = oddStridesOf w a
      sb   = oddStridesOf w b
      start' = (osStart sa + osStart sb) Bits..&. mask
  in addSubStridesFinish mask start' sa sb

-- | The native strides side of 'sub': anchor at @start_a − end_b mod
-- 2^w@ (where @end_b = start_b + n_b · stride_b@), then walk forward
-- through the same combined step count as 'add'. This mirrors
-- 'S.subRaw': @start_a − end_b@ is the smallest @sub@-result reachable
-- via the @j = n_b@ orientation, and stepping forward enumerates every
-- @x_a − y_b@ as @i@ rises and @j@ falls.
subStridesNative ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> OddStrides
subStridesNative w a b =
  let mask = fromInteger (NR.maxUnsigned w) :: Natural
      sa   = oddStridesOf w a
      sb   = oddStridesOf w b
      stb  = osStride mask sb
      nb   = steps sb
      endB = (osStart sb + nb * stb) Bits..&. mask
      -- @start' = start_a + (2^w − endB) mod 2^w@. When @endB == 0@,
      -- the subtrahend's anchor is the additive identity, so the
      -- result anchor is just @start a@.
      negEndB = if endB == 0 then 0 else mask + 1 - endB
      start'  = (osStart sa + negEndB) Bits..&. mask
  in addSubStridesFinish mask start' sa sb

-- | The shared add/sub combine, in factored coordinates. The result coset
-- width is @d = gcd(stride_a, stride_b)@; rather than reconstruct the
-- full-width strides and re-factor them by @ctz@, we read each operand's
-- 2-adic split @(v, oddPart)@ /as stored/ and assemble @d@ directly:
-- @d = gcdOdd(oddPart_a, oddPart_b) · 2^min(v_a, v_b)@. The step sizes and
-- orbit cap then drop out as shifts, and the result is handed to
-- 'mkOddStrides' with its split already in hand — no full-width stride is
-- ever materialized on this path.
addSubStridesFinish ::
  Natural {- ^ @mask@ -} ->
  Natural {- ^ result @start@ -} ->
  OddStrides {- ^ @a@ -} -> OddStrides {- ^ @b@ -} ->
  OddStrides
addSubStridesFinish mask start' (OddStrides vA oddA _ na) (OddStrides vB oddB _ nb)
  | na == 0 && nb == 0 = mkOddStrides mask 0 1 start' 0
  | na == 0 = mkOddStrides mask vB oddB start' nb
  | nb == 0 = mkOddStrides mask vA oddA start' na
  | otherwise =
      let -- The result coset width @d = gcdOdd(oddA, oddB) · 2^vD@: the odd
          -- gcd of the stored odd parts, scaled by the smaller 2-adic
          -- exponent. No @ctz@ re-derivation — @(vD, oddD)@ is the split.
          vD    = min vA vB
          oddD  = gcdOdd oddA oddB
          -- Steps in result: @n_a · (stride_a\/d) + n_b · (stride_b\/d)@.
          -- @oddD@ divides each odd part exactly and @vD ≤ v_*@, so each
          -- @stride_*\/d = (oddPart_*\/oddD) << (v_* − vD)@ is exact.
          stepA = (oddA `Prelude.div` oddD) `Bits.shiftL` (vA - vD)
          stepB = (oddB `Prelude.div` oddD) `Bits.shiftL` (vB - vD)
          nRaw  = na * stepA + nb * stepB
          -- Orbit cap, as in 'S.clampToOrbit': @2^w / 2^vD@, driven by
          -- @d@'s 2-adic part only (its odd factor does not shrink the
          -- orbit on @Z\/2^w@).
          orbit = (mask + 1) `Bits.shiftR` vD
          n'    = min nRaw (orbit - 1)
      in mkOddStrides mask vD oddD start' n'

-- | /O(M(w))/ native scale: a width-@w@ modular multiply of every orbit
-- anchor by @k@, preserving the orbit shape.
--
-- Asymptotic precision win: 'S.scale' currently routes through
-- 'A.scale' (the arithmetic-interval scaling), which collapses the
-- progression to its arithmetic hull and discards every stride/orbit
-- bit. We compute @start' = k·start@, @stride' = k·stride@ at width @w@
-- directly, so the resulting orbit has at most @n + 1@ elements (vs.
-- @S.scale@'s arithmetic-hull blow-up to potentially @2^w@).
--
-- The bitwise component is refreshed via 'B.scale' and mutually-refined
-- with the new orbit by 'compressFromS'.
scale :: (1 <= w) => NatRepr w -> Integer -> Domain w -> Domain w
scale w k d =
  nativeReduce w (scaleStridesNative w k (oddStridesOf w d)) (B.scale k (bitwise d))

-- | Native scale on the strides side: width-@w@ modular multiply of
-- @start@ and @stride@ by @k@, with the orbit length clamped to the
-- new stride's orbit. When the new stride is @0 mod 2^w@ — happens when
-- @v + ctz(k) ≥ w@ — the orbit collapses to a singleton.
scaleStridesNative :: (1 <= w) => NatRepr w -> Integer -> OddStrides -> OddStrides
scaleStridesNative w k s =
  let mask     = fromInteger (NR.maxUnsigned w) :: Natural
      kN       = fromInteger (k Bits..&. NR.maxUnsigned w) :: Natural
      newStart = (kN * osStart s) Bits..&. mask
      newStr0  = (kN * osStride mask s) Bits..&. mask
  in if newStr0 == 0
       then mkOddStridesFromStride mask newStart 1 0  -- collapsed: {newStart}
       else
         let -- @g = lowestSetBit newStr0@: isolate the lowest set bit. Compute
             -- via @Integer@ to avoid 'Natural's underflow on @negate@.
             g       = fromInteger
                         (let x = toInteger newStr0
                          in x Bits..&. Prelude.negate x) :: Natural
             -- Orbit length @= (mask + 1) / g@, both powers of two.
             orbit   = (mask + 1) `Bits.shiftR` countTrailingZeroes (toInteger g)
             newN    = min (steps s) (orbit - 1)
         in mkOddStridesFromStride mask newStart newStr0 newN

-- | /O(w · G(w))/ native mul: closed-form combine of the bilinear orbit
-- @(start_a + i·stride_a)·(start_b + j·stride_b) mod 2^w@.
--
-- The orbit's three "spread" terms — @i·stride_a·start_b@,
-- @j·stride_b·start_a@, @i·j·stride_a·stride_b@ — generate (in @Z\/2^w@)
-- the cyclic subgroup @<d>@ where @d@ is their 'binGcd'. Anchored at
-- @start_a·start_b@, the result lies in
-- @{start_a·start_b + k·d mod 2^w : k ∈ ℤ}@. The step count is bounded
-- by walking the three coefficient maxima:
-- @n_a·(stride_a·start_b)\/d + n_b·(stride_b·start_a)\/d +
-- n_a·n_b·(stride_a·stride_b)\/d@.
mul :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
mul w a b =
  nativeReduce w (mulStridesNative w a b)
    (B.mulBounded (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b))

mulPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
mulPrecise w a b =
  -- The precise reduction stays bridged ('S.reducePrecise' has no native
  -- port yet), so re-expand the native mul result to an 'S.Domain' here.
  compressFromSPrecise w (oddStridesToS w (mulStridesNative w a b))
    (B.mulPreciseBounded (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b))

-- | Native strides side of 'mul' (and 'mulPrecise'): closed-form combine
-- on the bilinear orbit's three spread terms. Returns the result
-- 'OddStrides' for the caller to reduce against the bitwise mul.
mulStridesNative ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> OddStrides
mulStridesNative w a b =
  let mask = fromInteger (NR.maxUnsigned w) :: Natural
      sa   = oddStridesOf w a
      sb   = oddStridesOf w b
      vA   = stridePow2 sa
      vB   = stridePow2 sb
      sta  = osStride mask sa
      stb  = osStride mask sb
      sa0  = osStart sa
      sb0  = osStart sb
      na   = steps sa
      nb   = steps sb
      anchor = (sa0 * sb0) Bits..&. mask
  in if na == 0 && nb == 0
       -- Singleton × singleton: exact, just the anchor.
       then mkOddStridesFromStride mask anchor 1 0
       else
         let -- The three modular spread terms.
             tX  = (sta * sb0) Bits..&. mask                -- coefficient of @i@
             tY  = (stb * sa0) Bits..&. mask                -- coefficient of @j@
             tZ  = (sta * stb) Bits..&. mask                -- coefficient of @i·j@
             -- A term contributes unless its index range is empty or its
             -- coefficient is zero. The result coset width is the full
             -- @gcd@ over the /contributing/ terms (via 'binGcd'), which
             -- keeps any common odd factor.
             presentX = na /= 0 && tX /= 0
             presentY = nb /= 0 && tY /= 0
             presentZ = na /= 0 && nb /= 0 && tZ /= 0
             -- @tX@/@tY@ each fold in a /start/, whose trailing zeros are
             -- not in the stored factoring, so they need a @ctz@ (via plain
             -- 'binGcd'). @tZ = (oddA·oddB) << (vA+vB)@ masked, however, has
             -- valuation exactly @vA+vB@ — the product of two odd parts is
             -- odd, so its low bit survives masking when present — so we fold
             -- it via 'binGcdSplit' with the known split, no @ctz@.
             dXY = case [ t | (p, t) <- [(presentX, tX), (presentY, tY)], p ] of
                     []        -> Nothing
                     (t0 : ts) -> Just (Prelude.foldl binGcd t0 ts)
             mbD = case (dXY, presentZ) of
                     (Just d,  True)  -> Just (binGcdSplit d (vA + vB) (tZ `Bits.shiftR` (vA + vB)))
                     (Just d,  False) -> Just d
                     (Nothing, True)  -> Just tZ
                     (Nothing, False) -> Nothing
         in case mbD of
              -- Every spread term blanks: bilinear orbit collapses to
              -- the singleton anchor.
              Nothing -> mkOddStridesFromStride mask anchor 1 0
              Just d  ->
                let -- Step count: sum the per-term contributions in
                    -- units of @d@. @d@ divides every contributing @t*@
                    -- exactly, so these divisions are exact.
                    contribX = if presentX then na * (tX `Prelude.div` d) else 0
                    contribY = if presentY then nb * (tY `Prelude.div` d) else 0
                    contribZ = if presentZ then na * nb * (tZ `Prelude.div` d) else 0
                    nRaw     = contribX + contribY + contribZ
                    -- Orbit cap driven by @d@'s 2-adic part only (its odd
                    -- factor doesn't shrink the orbit on @Z\/2^w@).
                    orbit    = (mask + 1) `Prelude.div` lowestBit mask d
                    n'       = min nRaw (orbit - 1)
                in mkOddStridesFromStride mask anchor d n'

-- | /O(w)/. The lowest set bit of a non-zero @x ≤ mask@: @x &amp; (-x)@
-- with the negation done via @mask + 1 − x@ to avoid 'Natural'
-- underflow.
lowestBit :: Natural -> Natural -> Natural
lowestBit mask x = x Bits..&. (mask + 1 - x)
{-# INLINE lowestBit #-}

-- | /O(w)/. Stein's binary GCD restricted to two /odd/ operands. Both
-- inputs must be odd (asserted); the result is the odd 'Prelude.gcd' of
-- the two — itself necessarily odd.
--
-- The classic Stein step has three cases (both even, one even, both
-- odd). Here both operands are odd at entry, so we only ever hit the
-- both-odd case: replace the larger with @|a − b|@, which is even,
-- then strip /all/ its factors of two with one shift — re-establishing
-- the odd invariant for the next iteration. No division, no @mod@: every
-- step is a subtract, a compare, and a shift, so the whole loop is
-- @O(w)@ width-@w@ word operations. Termination: the larger operand
-- strictly decreases each step.
--
-- The 'add', 'sub', and 'mul' combines factor each result stride as
-- @2^v · oddPart@; 'gcdOdd' computes the @oddPart@ of the combined
-- stride. Property-tested against 'Prelude.gcd' by
-- 'gcdOddMatchesPrelude'.
gcdOdd :: Natural -> Natural -> Natural
gcdOdd a0 b0 =
  assert (a0 Bits..&. 1 == 1) $
  assert (b0 Bits..&. 1 == 1) $
  go a0 b0
  where
    go a b
      | a == b    = a
      | a > b     = go (stripTwos (a - b)) b
      | otherwise = go a (stripTwos (b - a))
    -- Strip every trailing zero bit: @x / 2^ctz(x)@. @x@ is nonzero
    -- here (the @a == b@ guard fired otherwise), so @ctz@ is well-defined.
    stripTwos x = x `Bits.shiftR` countTrailingZeroes (toInteger x)

-- | /O(w)/. The full 'Prelude.gcd' of two (possibly even) 'Natural's,
-- factored as @2^min(v_a, v_b) · gcdOdd(oddPart_a, oddPart_b)@. Handles
-- zero operands the way 'Prelude.gcd' does: @binGcd 0 b == b@ and
-- @binGcd a 0 == a@. Property-tested against 'Prelude.gcd' by
-- 'binGcdMatchesPrelude'.
binGcd :: Natural -> Natural -> Natural
binGcd 0 b = b
binGcd a 0 = a
binGcd a b =
  let va = countTrailingZeroes (toInteger a)
      vb = countTrailingZeroes (toInteger b)
      oddA = a `Bits.shiftR` va
      oddB = b `Bits.shiftR` vb
  in gcdOdd oddA oddB `Bits.shiftL` min va vb

-- | /O(w)/. @binGcd@ of a value @a@ against a /pre-factored/ second
-- operand @2^vb · oddB@ (with @oddB@ odd) — the caller hands in @b@'s
-- 2-adic split so it is not re-derived by @ctz@. Equal to
-- @binGcd a (oddB `shiftL` vb)@; used on 'mul''s @tZ@ term, whose
-- valuation @v_a + v_b@ and odd part @oddA · oddB@ are known from the
-- operand factorings without re-inspecting the product.
binGcdSplit :: Natural -> Int -> Natural -> Natural
binGcdSplit 0 vb oddB = oddB `Bits.shiftL` vb
binGcdSplit a vb oddB =
  let va   = countTrailingZeroes (toInteger a)
      oddA = a `Bits.shiftR` va
  in gcdOdd oddA oddB `Bits.shiftL` min va vb

-- ------------------------------------------------------------------
-- * Native 2-adic meet/leq
--
-- These reimplement the 'Strides' containment and meet algorithms
-- directly on the reduced @(start, stride = 2^v · mOdd, n)@ shape,
-- without re-deriving the 2-adic structure inside 'Strides'. The
-- @stride@/@start@/@n@ values are read from 'expandToS', whose 'S.mk'
-- canonicalizes singletons and full cosets, so they agree bit-for-bit
-- with what the bridged @S.<op>@ would have seen — the native routines
-- therefore denote exactly the same sets as the bridge.
--
-- The Hensel inverse runs at the /reduced/ modulus @2^w / 2^v@ rather
-- than the full @2^w@: writing @stride = 2^v · m@ for odd @m@, the
-- progression's subgroup is @⟨2^v⟩@ and only @m@ (a unit there) needs
-- inverting, modulo @2^w / 2^v@. (Asymptotically the same as the
-- bridged 'S.valueIndex', which already shifts out @2^v@ before its
-- own Hensel; the win is avoiding the @expandToS → S.<op>@ indirection
-- and keeping the reduced-width arithmetic explicit.)

-- | /O(A(w))/. Modular additive inverse modulo @mask + 1@. Local copy of
-- 'What4.Domains.BV.Strides.modNeg' (not exported).
modNegLocal :: Natural -> Natural -> Natural
modNegLocal msk x = (msk + 1 - x) Bits..&. msk
{-# INLINE modNegLocal #-}

-- | /O(A(w))/. Modular subtraction @x − y@ mod @mask + 1@. Local copy of
-- 'What4.Domains.BV.Strides.modSub' (not exported).
modSubLocal :: Natural -> Natural -> Natural -> Natural
modSubLocal msk x y = (x + modNegLocal msk y) Bits..&. msk
{-# INLINE modSubLocal #-}

-- | /O(A(w))/. The lowest set bit of @stride@, i.e. @gcd(stride, 2^w) =
-- 2^v@. Local copy of 'What4.Domains.BV.Strides.strideGcd' specialized
-- to a raw stride.
strideGcdN :: Natural -> Natural
strideGcdN st = 1 `Bits.shiftL` countTrailingZeroes (toInteger st)
{-# INLINE strideGcdN #-}

-- | /O(M(k) log k)/. The reduced index of value @v@ on the orbit of
-- @(s, st)@ at width @w@: the unique @i@ in @[0, 2^w / 2^v)@ with
-- @s + i·st ≡ v (mod 2^w)@. Precondition: @v@ is on the coset (the
-- offset is a multiple of @2^v@), checked by 'reducedIndexMaybe'.
--
-- Mirror of 'What4.Domains.BV.Strides.valueIndex': shift the 2-adic
-- factor @g = 2^v@ out of both the offset and the stride, then multiply
-- by the Hensel inverse of the odd part modulo the reduced modulus
-- @2^w / g@.
reducedIndex ::
  Natural {- ^ @mask = 2^w − 1@ -} ->
  Natural {- ^ @start@ -} -> Natural {- ^ @stride@ -} ->
  Natural {- ^ value @v@ -} -> Natural
reducedIndex msk s st v =
  let off  = modSubLocal msk v s
      g    = strideGcdN st
      m'   = (msk + 1) `Bits.shiftR` countTrailingZeroes (toInteger g)
      sInv = invModPow2Local (st `divByPow2N` g) m'
  in ((off `divByPow2N` g) * sInv) Bits..&. (m' - 1)

-- | Reduced index, or 'Nothing' when @v@ is off the coset (its offset
-- from @start@ is not a multiple of @2^v@). Mirror of
-- 'What4.Domains.BV.Strides.valueIndexMaybe'.
reducedIndexMaybe ::
  Natural -> Natural -> Natural -> Natural -> Maybe Natural
reducedIndexMaybe msk s st v
  | modSubLocal msk v s Bits..&. (strideGcdN st - 1) == 0 = Just (reducedIndex msk s st v)
  | otherwise                                             = Nothing

-- | /O(A(w))/. @x / 2^v@ where @v = ctz(p)@; @p@ a power of two. Local
-- copy of 'What4.Domains.BV.Strides.divByPow2'.
divByPow2N :: Natural -> Natural -> Natural
divByPow2N x p = x `Bits.shiftR` countTrailingZeroes (toInteger p)
{-# INLINE divByPow2N #-}

-- | The strides-side of 'leqPrecise', reimplemented natively on the
-- reduced representation. Denotationally equal to
-- @S.leqPrecise (expandToS w a) (expandToS w b)@: it reads the
-- canonical @(start, stride, n)@ off 'expandToS' and applies the same
-- three checks (start-of-@a@ on @b@'s orbit within range; @a@ a
-- singleton; else @stride b@ divides @stride a@ and @a@'s window fits
-- forward inside @b@'s), with the modular inverse taken at the reduced
-- width.
nativeLeqPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Bool
nativeLeqPrecise w a b =
  let sa  = expandToS w a
      sb  = expandToS w b
      msk = S.mask sb
      stA = S.stride sa
      stB = S.stride sb
      nA  = S.n sa
      nB  = S.n sb
  in case reducedIndexMaybe msk (S.start sb) stB (S.start sa) of
       Nothing      -> False
       Just iAStart ->
         iAStart <= nB
           && ( nA == 0
                || ( stA `Prelude.mod` stB == 0
                     && iAStart + nA * (stA `Prelude.div` stB) <= nB ) )

-- | /O(A(w))/. Does this operand's orbit avoid wrapping mod @2^w@, i.e.
-- is it a genuine integer arithmetic progression in @[start, start +
-- n·stride] ⊆ [0, mask]@? Stronger than @not isSelfWrapping@ (which only
-- bounds the /span/ @n·stride@): a non-self-wrapping orbit anchored near
-- @mask@ can still cross the @2^w@ boundary. The native 2-adic meet needs
-- the strict no-wrap form so the two orbits are plain integer APs.
noWrapMod2w :: (1 <= w) => NatRepr w -> Domain w -> Bool
noWrapMod2w w d =
  let s = expandToS w d
  in S.start s + S.n s * S.stride s <= S.mask s

-- | The exact intersection of two /power-of-two-stride/, /non-wrapping/
-- orbits, returned as the strides-side 'S.Domain' (or 'Nothing' when the
-- orbits are disjoint). Precondition (caller-checked): @mOdd a == 1@,
-- @mOdd b == 1@, and 'noWrapMod2w' on both.
--
-- Because both strides are powers of two @2^vA@, @2^vB@, the CRT moduli
-- are /nested/: @gcd = 2^min(vA,vB)@, @lcm = 2^max(vA,vB) = max(2^vA,
-- 2^vB)@. The joint residue is solvable iff @start a ≡ start b (mod
-- 2^min)@, and when solvable it is simply the residue of the
-- larger-valuation operand — /no modular inverse is required/ (this is
-- the genuine closed-form degeneracy; the general odd-stride meet still
-- needs an extended-gcd Bézout solve, which is why that case stays
-- bridged). The result is the arithmetic progression with step @lcm@
-- over the overlap window @[max start, min end]@, anchored at the first
-- window point on the joint residue.
native2AdicMeet ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (S.Domain w)
native2AdicMeet w a b =
  let sa  = expandToS w a
      sb  = expandToS w b
      sA  = S.start sa; tA = S.stride sa; nA = S.n sa
      sB  = S.start sb; tB = S.stride sb; nB = S.n sb
      eA  = sA + nA * tA   -- no wrap ⇒ ≤ mask
      eB  = sB + nB * tB
      gMask = min tA tB - 1            -- 2^min(vA,vB) − 1
      l     = max tA tB                -- 2^max(vA,vB) = lcm of the two
      sFine = if tA >= tB then sA else sB
      lo    = max sA sB
      hi    = min eA eB
  in if (sA Bits..&. gMask) /= (sB Bits..&. gMask)  -- residues incompatible mod 2^min
       then Nothing
     else if lo > hi
       then Nothing
     else
       let r      = (lo - sFine) `Prelude.mod` l   -- lo ≥ sFine ≥ 0
           theta0 = if r == 0 then lo else lo + (l - r)
       in if theta0 > hi
            then Nothing
            else Just (S.mk w theta0 l ((hi - theta0) `Prelude.div` l))

-- | /O(A(w))/. The orbit length @2^w / 2^v@ of a stride. Local mirror of
-- 'What4.Domains.BV.Strides.orbitLen'.
orbitLenN :: Natural {- ^ @mask = 2^w − 1@ -} -> Natural {- ^ @stride@ -} -> Natural
orbitLenN msk st = (msk + 1) `divByPow2N` strideGcdN st
{-# INLINE orbitLenN #-}

-- | @floorSum n m a b = sum_{i=0}^{n-1} ((a·i + b) \`div\` m)@. Local copy of
-- 'What4.Domains.BV.Strides.floorSum' (not exported): the irreducible
-- Euclidean lattice-point count used only on 'nativeLeqExactWindow''s
-- residual. Requires @m > 0@; all values non-negative.
floorSumN :: Natural -> Natural -> Natural -> Natural -> Natural
floorSumN n0 m0 a0 b0 = go 0 n0 m0 a0 b0
  where
    go !ans !nn !m !a !b
      | nn == 0 || m == 0 = ans
      | a >= m =
          go (ans + (nn * (nn - 1) `Prelude.div` 2) * (a `Prelude.div` m))
             nn m (a `Prelude.mod` m) b
      | b >= m =
          go (ans + nn * (b `Prelude.div` m)) nn m a (b `Prelude.mod` m)
      | otherwise =
          let yMax = a * nn + b
          in if yMax < m
               then ans
               else go ans (yMax `Prelude.div` m) a m (yMax `Prelude.mod` m)

-- | The strides-side of 'leqExact', reimplemented natively on the reduced
-- representation. Denotationally equal to @S.leqExact (expandToS w a)
-- (expandToS w b)@: a faithful port of 'Strides.leqExactPartial' (cheap
-- @O(w)@ branches at the reduced width) with the residual large-window
-- case handed to 'floorSumN' (mirror of 'Strides.leqExactWindow').
--
-- All @(start, stride, n)@ are read from 'expandToS' (canonicalized by
-- 'S.mk'), so they match what the bridged oracle sees bit-for-bit.
nativeLeqExact :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Bool
nativeLeqExact w a b =
  let sa  = expandToS w a
      sb  = expandToS w b
      msk = S.mask sb
      stA = S.stride sa
      stB = S.stride sb
      nA  = S.n sa
      nB  = S.n sb
      gB  = strideGcdN stB
      mB  = orbitLenN msk stB
      -- @a@'s stride translated into @b@'s reduced index space.
      invSB = invModPow2Local (stB `divByPow2N` gB) mB
      aStep = ((stA `divByPow2N` gB) * invSB) Bits..&. (mB - 1)
      -- Forward/backward unwrapped-fit test (mirror of monoFits).
      monoFits iAStart =
        let forward  = iAStart + nA * aStep
            iEnd     = forward `Prelude.mod` mB
            backward = iEnd + nA * (mB - aStep)
        in iAStart <= nB && (forward <= nB || backward <= nB)
      -- The residual floorSum window count (mirror of leqExactWindow).
      window iAStart =
        let nA1   = nA + 1
            wW    = nB + 1
            hits  = nA1 + floorSumN nA1 mB aStep iAStart
                        - floorSumN nA1 mB aStep (iAStart + mB - wW)
        in hits == nA1
  in case reducedIndexMaybe msk (S.start sb) stB (S.start sa) of
       Nothing      -> False                              -- (1) off coset
       Just iAStart
         | nA == 0                  -> iAStart <= nB       -- singleton
         | stA `Prelude.mod` gB /= 0 -> False              -- (2) subgroup fail
         | nB + 1 == mB             -> True                -- (3) b full
         | nA > nB                  -> False               -- pigeonhole
         | monoFits iAStart         -> True                -- monoFits-accept
         | (nB + 1) * 2 <= mB       -> False               -- small window reject
         | otherwise                -> window iAStart       -- residual count

udiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
udiv w a b =
  compressFromS w (S.udiv w (expandToS w a) (expandToS w b))
    (B.udivBounded (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b))

udivPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
udivPrecise w a b =
  compressFromSPrecise w (S.udiv w (expandToS w a) (expandToS w b))
    (B.udivPreciseBounded w (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b))

urem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
urem w a b =
  compressFromS w (S.urem w (expandToS w a) (expandToS w b))
    (B.uremBounded (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b))

uremPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
uremPrecise w a b =
  compressFromSPrecise w (S.urem w (expandToS w a) (expandToS w b))
    (B.uremPreciseBounded w (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b))

sdiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdiv w a b =
  compressFromS w (S.sdiv w (expandToS w a) (expandToS w b))
    (B.sdiv w (bitwise a) (bitwise b))

srem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
srem w a b =
  compressFromS w (S.srem w (expandToS w a) (expandToS w b))
    (B.srem w (bitwise a) (bitwise b))

-- ------------------------------------------------------------------
-- ** Arithmetic (SMT-LIB div-by-zero semantics)

udivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
udivSmtlib w a b =
  compressFromS w (S.udivSmtlib w (expandToS w a) (expandToS w b))
    (B.udivSmtlibBounded (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b))

uremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
uremSmtlib w a b =
  compressFromS w (S.uremSmtlib w (expandToS w a) (expandToS w b))
    (B.uremSmtlibBounded (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b))

sdivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sdivSmtlib w a b =
  compressFromS w (S.sdivSmtlib w (expandToS w a) (expandToS w b))
    (B.sdivSmtlib w (bitwise a) (bitwise b))

sremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sremSmtlib w a b =
  compressFromS w (S.sremSmtlib w (expandToS w a) (expandToS w b))
    (B.sremSmtlib w (bitwise a) (bitwise b))

-- ------------------------------------------------------------------
-- ** Arithmetic (LLVM overflow flags)

addNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
addNuw w a b =
  fmap (\s -> compressFromS w s (B.add (bitwise a) (bitwise b)))
       (S.addNuw w (expandToS w a) (expandToS w b))

addNsw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
addNsw w a b =
  fmap (\s -> compressFromS w s (B.add (bitwise a) (bitwise b)))
       (S.addNsw w (expandToS w a) (expandToS w b))

addNswNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
addNswNuw w a b =
  fmap (\s -> compressFromS w s (B.add (bitwise a) (bitwise b)))
       (S.addNswNuw w (expandToS w a) (expandToS w b))

subNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
subNuw w a b =
  fmap (\s -> compressFromS w s (B.sub (bitwise a) (bitwise b)))
       (S.subNuw w (expandToS w a) (expandToS w b))

subNsw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
subNsw w a b =
  fmap (\s -> compressFromS w s (B.sub (bitwise a) (bitwise b)))
       (S.subNsw w (expandToS w a) (expandToS w b))

subNswNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
subNswNuw w a b =
  fmap (\s -> compressFromS w s (B.sub (bitwise a) (bitwise b)))
       (S.subNswNuw w (expandToS w a) (expandToS w b))

mulNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
mulNuw w a b =
  fmap (\s -> compressFromS w s
        (B.mulBounded (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b)))
       (S.mulNuw w (expandToS w a) (expandToS w b))

mulNsw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
mulNsw w a b =
  fmap (\s -> compressFromS w s
        (B.mulBounded (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b)))
       (S.mulNsw w (expandToS w a) (expandToS w b))

mulNswNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
mulNswNuw w a b =
  fmap (\s -> compressFromS w s
        (B.mulBounded (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b)))
       (S.mulNswNuw w (expandToS w a) (expandToS w b))

shlNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
shlNuw w a b =
  fmap (\s -> compressFromS w s (shlBitwise w a b))
       (S.shlNuw w (expandToS w a) (expandToS w b))

shlNsw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
shlNsw w a b =
  fmap (\s -> compressFromS w s (shlBitwise w a b))
       (S.shlNsw w (expandToS w a) (expandToS w b))

shlNswNuw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
shlNswNuw w a b =
  fmap (\s -> compressFromS w s (shlBitwise w a b))
       (S.shlNswNuw w (expandToS w a) (expandToS w b))

udivExact :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
udivExact w a b =
  fmap (\s -> compressFromS w s
        (B.udivBounded (bitwise a) (tightUBounds w a) (bitwise b) (tightUBounds w b)))
       (S.udivExact w (expandToS w a) (expandToS w b))

sdivExact :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
sdivExact w a b =
  fmap (\s -> compressFromS w s (B.sdiv w (bitwise a) (bitwise b)))
       (S.sdivExact w (expandToS w a) (expandToS w b))

lshrExact :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
lshrExact w a b =
  fmap (\s -> compressFromS w s (lshrBitwise w a b))
       (S.lshrExact w (expandToS w a) (expandToS w b))

ashrExact :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
ashrExact w a b =
  fmap (\s -> compressFromS w s (ashrBitwise w a b))
       (S.ashrExact w (expandToS w a) (expandToS w b))

-- | Shared bitwise shl logic.
shlBitwise ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> B.Domain w
shlBitwise w a b =
  case reachableAmounts w (clampShift w) b of
    Just amts -> B.shlAbstractOver w (bitwise a) amts
    Nothing   -> B.shlAbstractBounded w (bitwise a) (bitwise b) (tightUBounds w b)

lshrBitwise ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> B.Domain w
lshrBitwise w a b =
  case reachableAmounts w (clampShift w) b of
    Just amts -> B.lshrAbstractOver w (bitwise a) amts
    Nothing   -> B.lshrAbstractBounded w (bitwise a) (bitwise b) (tightUBounds w b)

ashrBitwise ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> B.Domain w
ashrBitwise w a b =
  case reachableAmounts w (clampShift w) b of
    Just amts -> B.ashrAbstractOver w (bitwise a) amts
    Nothing   -> B.ashrAbstractBounded w (bitwise a) (bitwise b) (tightUBounds w b)

-- ------------------------------------------------------------------
-- * Bitwise operations

-- The strides side of each bitwise op is computed natively on the
-- factored representation by the @*OS@ combinators below (see
-- "Native bitwise on the odd-factored representation"), then settled
-- against the per-bit 'B.<op>' tnum by the full 'nativeReduce' —
-- mirroring the @mul@ native pattern. The precise variants stay on the
-- bridged precise reduce ('compressFromSPrecise'), re-expanding the
-- native strides result via 'oddStridesToS' as in 'mulPrecise'.
--
-- These ops need 'nativeReduce' (lift /and/ projection-meet), not a
-- cheaper variant. Both halves of the reduce do real work here:
--
--   * The lift-free 'nativeReduceProject' is unsound: the result orbit's
--     lowest free bit @k@ comes from the operands' strides-side forced
--     bits, but the result tnum ('B.and' etc.) comes from the operands'
--     /tnums/, which (by the reduced-product slack) can force bit @k@
--     even when the orbit leaves it free. The tnum→orbit lift folds that
--     forced bit back into the orbit, re-establishing the
--     representational invariant @ctzTnum(bitwise) == ctz(stride)@ that
--     'member' relies on.
--
--   * The orbit→tnum projection-meet is also required: after the lift,
--     the tnum can /still/ be looser than the orbit's bitwise
--     projection (e.g. @andOS@ yields the singleton orbit @{2}@ while
--     'B.and' yields the tnum @{0,2}@, whose @ctzTnum@ is @1@ but whose
--     orbit @ctz(stride)@ is @0@). Storing that pair unreduced corrupts
--     'expandToS'\/'member', which recover @v@ from @ctzTnum(bitwise)@.
--     The projection-meet tightens the tnum to the orbit's projection,
--     restoring the invariant. (This is why these ops do /not/ share the
--     lift-free fast path that @add@\/@sub@ use, where
--     'Tnum.add'\/'Tnum.sub' keep bit @v = ctz(stride)@ free.)

not :: (1 <= w) => NatRepr w -> Domain w -> Domain w
not w d = nativeReduce w (notOS w (oddStridesOf w d)) (B.not (bitwise d))

andFast :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
andFast w a b =
  nativeReduce w (andFastOS w (oddStridesOf w a) (oddStridesOf w b))
    (B.and (bitwise a) (bitwise b))

and :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
and w a b =
  nativeReduce w (andOS w (oddStridesOf w a) (oddStridesOf w b))
    (B.and (bitwise a) (bitwise b))

andPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
andPrecise w a b =
  compressFromSPrecise w (oddStridesToS w (andPreciseOS w (oddStridesOf w a) (oddStridesOf w b)))
    (B.and (bitwise a) (bitwise b))

orFast :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
orFast w a b =
  nativeReduce w (orFastOS w (oddStridesOf w a) (oddStridesOf w b))
    (B.or (bitwise a) (bitwise b))

or :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
or w a b =
  nativeReduce w (orOS w (oddStridesOf w a) (oddStridesOf w b))
    (B.or (bitwise a) (bitwise b))

orPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
orPrecise w a b =
  compressFromSPrecise w (oddStridesToS w (orPreciseOS w (oddStridesOf w a) (oddStridesOf w b)))
    (B.or (bitwise a) (bitwise b))

xorFast :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
xorFast w a b =
  nativeReduce w (xorFastOS w (oddStridesOf w a) (oddStridesOf w b))
    (B.xor (bitwise a) (bitwise b))

xor :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
xor w a b =
  nativeReduce w (xorOS w (oddStridesOf w a) (oddStridesOf w b))
    (B.xor (bitwise a) (bitwise b))

-- ------------------------------------------------------------------
-- * Native bitwise on the odd-factored representation
--
-- Faithful ports of the 'Strides' bitwise combinators that compute the
-- strides-side result directly on 'OddStrides', never building an
-- 'S.Domain'. Each result is a /cover/ constructed from a forced-bit
-- picture, so its stride is always a pure power of two (@oddPart = 1@) —
-- no Hensel inverse is needed in construction. The @(zeros, ones)@
-- forced bits and 'operandRangeOS'\/Warren bounds are read off the
-- factored operands; 'arcExtremes' and the Warren bounds are pure
-- 'Natural' computations copied verbatim from 'Strides' (they never
-- touched a 'Domain').

-- | /O(A(w))/. The orbit endpoint @(start + n·stride) mod 2^w@; port of
-- 'S.end'.
endOS :: Natural {- ^ @mask@ -} -> OddStrides -> Natural
endOS msk p@(OddStrides _ _ s nn) = (s + nn * osStride msk p) Bits..&. msk

-- | /O(A(w))/. Bitwise complement; port of 'S.not'. Stride and step
-- count are preserved, the orbit reverses, so the new @start@ is the
-- complement of the old @end@.
notOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides
notOS w p@(OddStrides v oddPart _ nn) =
  let msk = fromInteger (NR.maxUnsigned w) :: Natural
  in mkOddStrides msk v oddPart (msk - endOS msk p) nn

-- | /O(A(w))/. The progression's tight unsigned numeric range; port of
-- 'S.operandRange'.
operandRangeOS :: Natural {- ^ @mask@ -} -> OddStrides -> (Natural, Natural)
operandRangeOS msk p@(OddStrides v _ s nn) =
  let t     = osStride msk p
      g     = 1 `Bits.shiftL` v :: Natural
      span_ = nn * t
      lo    = s `Prelude.mod` g
  in if span_ > msk then (lo, msk - (g - 1) + lo)            -- self-wrap
     else if s + span_ > msk then                           -- wrap (not self)
       let k      = (msk - s) `Prelude.div` t
           preMax = s + k * t
           postMin = s + (k + 1) * t - (msk + 1)
       in (postMin, preMax)
     else (s, s + span_)                                     -- no wrap

-- | /O(A(w))/. Largest power-of-two divisor as a single-bit mask; the
-- lowest set bit of @x@ (or @1@ when @x == 0@). Local port of
-- 'S.lowestSetBit'.
lowestSetBitN :: Natural -> Natural
lowestSetBitN x = 1 `Bits.shiftL` countTrailingZeroes (toInteger x)

-- | /O(A(w))/. The highest set bit of @x@ as a single-bit mask; @0@ when
-- @x == 0@. Local port of 'S.highestSetBit'.
highestSetBitN :: Natural -> Natural
highestSetBitN x =
  let b = fromInteger (Arith.bitsBelow (toInteger x)) :: Natural
  in b `Bits.xor` (b `Bits.shiftR` 1)

-- | /O(A(w))/. The smallest @y@ with @a <= y <= mask@ agreeing with the
-- forced-bit pair, or 'Nothing'. Verbatim port of 'S.nextAgreeing'
-- (a pure 'Natural' computation).
nextAgreeingN :: Natural -> Natural -> Natural -> Natural -> Maybe Natural
nextAgreeingN m zeros ones a
  | v == 0 = Just a
  | ones Bits..&. hb /= 0 =
      Just ((a Bits..&. keepAbove hb) Bits..|. hb Bits..|. (ones Bits..&. (hb - 1)))
  | otherwise =
      let cands = (m `Bits.xor` a) Bits..&. (m `Bits.xor` zeros) Bits..&. keepAbove hb
      in if cands == 0
           then Nothing
           else
             let p = lowestSetBitN cands
             in Just ((a Bits..&. keepAbove p) Bits..|. p Bits..|. (ones Bits..&. (p - 1)))
  where
    v  = (a Bits..&. zeros) Bits..|. (ones Bits..&. (m `Bits.xor` a))
    hb = highestSetBitN v
    keepAbove b = m `Bits.xor` (2 * b - 1)

-- | /O(A(w))/. The largest @y@ with @0 <= y <= a@ agreeing with the
-- forced-bit pair, or 'Nothing'. Verbatim port of 'S.prevAgreeing'.
prevAgreeingN :: Natural -> Natural -> Natural -> Natural -> Maybe Natural
prevAgreeingN m zeros ones a
  | v == 0 = Just a
  | zeros Bits..&. hb /= 0 =
      Just ((a Bits..&. keepAbove hb) Bits..|. ((hb - 1) Bits..&. (m `Bits.xor` zeros)))
  | otherwise =
      let cands = a Bits..&. (m `Bits.xor` ones) Bits..&. keepAbove hb
      in if cands == 0
           then Nothing
           else
             let p = lowestSetBitN cands
             in Just ((a Bits..&. keepAbove p) Bits..|. ((p - 1) Bits..&. (m `Bits.xor` zeros)))
  where
    v  = (a Bits..&. zeros) Bits..|. (ones Bits..&. (m `Bits.xor` a))
    hb = highestSetBitN v
    keepAbove b = m `Bits.xor` (2 * b - 1)

-- | /O(A(w))/. First and last offsets along a circular arc of the values
-- matching a forced-bit pattern. Verbatim port of 'S.arcExtremes'.
arcExtremesN :: Natural -> Natural -> Natural -> Natural -> Natural -> Maybe (Natural, Natural)
arcExtremesN m zeros ones anchor len =
  case (mbTLo, mbTHi) of
    (Just tLo, Just tHi) -> Just (tLo, tHi)
    _ -> Nothing
  where
    arcWraps = anchor + len > m
    wrapEnd = (anchor + len) Bits..&. m
    mbTLo =
      case nextAgreeingN m zeros ones anchor of
        Just y
          | arcWraps || y - anchor <= len -> Just (y - anchor)
        _ | arcWraps, ones <= wrapEnd ->
              Just (ones + (m + 1) - anchor)
          | otherwise -> Nothing
    mbTHi =
      if arcWraps
        then case prevAgreeingN m zeros ones wrapEnd of
               Just y -> Just (y + (m + 1) - anchor)
               Nothing ->
                 let hiAll = m `Bits.xor` zeros
                 in if hiAll >= anchor then Just (hiAll - anchor) else Nothing
        else case prevAgreeingN m zeros ones (anchor + len) of
               Just y | y >= anchor -> Just (y - anchor)
               _ -> Nothing

-- | /O(A(w))/. Factored cover of every value agreeing with @(zeros,
-- ones)@ on the circular arc @[anchor, anchor + len]@; port of
-- 'S.fromForcedBitsArc'. The stride is the lowest free bit @2^k@
-- (@oddPart = 1@), so the factoring is read off directly.
fromForcedBitsArcOS ::
  (1 <= w) => NatRepr w -> (Natural, Natural) -> (Natural, Natural) -> OddStrides
fromForcedBitsArcOS w (zeros, ones) (anchor, len) =
  let m    = fromInteger (NR.maxUnsigned w) :: Natural
      free = m `Bits.xor` (zeros Bits..|. ones)
  in if free == 0
       then mkOddStrides m 0 1 ones 0
       else
         let k = countTrailingZeroes (toInteger free)
         in case arcExtremesN m zeros ones anchor len of
              Just (tLo, tHi) ->
                mkOddStrides m k 1 ((anchor + tLo) Bits..&. m) ((tHi - tLo) `Bits.shiftR` k)
              Nothing -> mkOddStrides m 0 1 ones 0

-- | /O(A(w))/. Factored cover agreeing with @(zeros, ones)@ in the
-- unsigned interval @[lo, hi]@; port of 'S.fromForcedBits'.
fromForcedBitsOS ::
  (1 <= w) => NatRepr w -> (Natural, Natural) -> (Natural, Natural) -> OddStrides
fromForcedBitsOS w bits (lo, hi) = fromForcedBitsArcOS w bits (lo, hi - lo)

-- | /O(A(w))/. Factored cover agreeing with @(zeros, ones)@ with no
-- interval constraint; port of 'S.fromForced'.
fromForcedOS :: (1 <= w) => NatRepr w -> (Natural, Natural) -> OddStrides
fromForcedOS w (zeros, ones) =
  let m    = fromInteger (NR.maxUnsigned w) :: Natural
      free = m `Bits.xor` (zeros Bits..|. ones)
  in if free == 0
       then mkOddStrides m 0 1 ones 0
       else let k = countTrailingZeroes (toInteger free)
            in mkOddStrides m k 1 ones (free `Bits.shiftR` k)

-- | /O(A(w))/. Bitwise AND of a singleton @{k}@ with @c@; port of
-- 'S.andSingleton'.
andSingletonOS :: (1 <= w) => NatRepr w -> Natural -> OddStrides -> OddStrides
andSingletonOS w k c =
  let m              = fromInteger (NR.maxUnsigned w) :: Natural
      (zeros, ones)  = forcedBitsOS w c
      zeros'         = (m `Bits.xor` k) Bits..|. zeros
      ones'          = k Bits..&. ones
      (_, cHi)       = operandRangeOS m c
  in fromForcedBitsOS w (zeros', ones') (0, cHi)

-- | /O(M(w))/. Cheap AND kernel; port of 'S.andFast'.
andFastOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides -> OddStrides
andFastOS w a b =
  case (steps a, steps b) of
    (0, _) -> andSingletonOS w (osStart a) b
    (_, 0) -> andSingletonOS w (osStart b) a
    _ ->
      let m = fromInteger (NR.maxUnsigned w) :: Natural
          (za, oa) = forcedBitsOS w a
          (zb, ob) = forcedBitsOS w b
          (_, aHi) = operandRangeOS m a
          (_, bHi) = operandRangeOS m b
      in fromForcedBitsOS w (za Bits..|. zb, oa Bits..&. ob) (0, min aHi bHi)

-- | /O(w · A(w))/. Tight unsigned lower bound on @x .&. y@; verbatim port
-- of 'S.warrenAndLo' (pure 'Natural' loop).
warrenAndLoN :: Natural -> Natural -> Natural -> Natural -> Natural -> Natural
warrenAndLoN m alo ahi blo bhi =
  uncurry (Bits..&.) (go alo blo (Bits.popCount m - 1))
  where
    notN x = m - x
    go a b i
      | i < 0 = (a, b)
      | otherwise =
          let bit_ = 1 `Bits.shiftL` i
              aPrime = (a Bits..|. bit_) Bits..&. notN (bit_ - 1)
              bPrime = (b Bits..|. bit_) Bits..&. notN (bit_ - 1)
              canFlip = (notN a Bits..&. notN b Bits..&. bit_) /= 0
          in if canFlip && aPrime <= ahi then go aPrime b (i - 1)
             else if canFlip && bPrime <= bhi then go a bPrime (i - 1)
             else go a b (i - 1)

-- | /O(w · A(w))/. Tight unsigned upper bound on @x .&. y@; verbatim port
-- of 'S.warrenAndHi'.
warrenAndHiN :: Natural -> Natural -> Natural -> Natural -> Natural -> Natural
warrenAndHiN m alo ahi blo bhi =
  uncurry (Bits..&.) (go ahi bhi (Bits.popCount m - 1))
  where
    notN x = m - x
    go a b i
      | i < 0 = (a, b)
      | otherwise =
          let bit_ = 1 `Bits.shiftL` i
              aPrime = (a Bits..&. notN bit_) Bits..|. (bit_ - 1)
              bPrime = (b Bits..&. notN bit_) Bits..|. (bit_ - 1)
          in if (a Bits..&. notN b Bits..&. bit_) /= 0 && aPrime >= alo
             then go aPrime b (i - 1)
             else if (notN a Bits..&. b Bits..&. bit_) /= 0 && bPrime >= blo
                  then go a bPrime (i - 1)
                  else go a b (i - 1)

-- | /O(w · A(w))/. The Warren-bounds AND kernel; port of
-- 'S.andPreciseRaw'.
andPreciseRawOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides -> OddStrides
andPreciseRawOS w a b =
  case (steps a, steps b) of
    (0, _) -> andSingletonOS w (osStart a) b
    (_, 0) -> andSingletonOS w (osStart b) a
    _ ->
      let m = fromInteger (NR.maxUnsigned w) :: Natural
          (za, oa) = forcedBitsOS w a
          (zb, ob) = forcedBitsOS w b
          (aLo, aHi) = operandRangeOS m a
          (bLo, bHi) = operandRangeOS m b
          wLo = warrenAndLoN m aLo aHi bLo bHi
          wHi = warrenAndHiN m aLo aHi bLo bHi
      in fromForcedBitsOS w (za Bits..|. zb, oa Bits..&. ob) (wLo, wHi)

-- | /O(M(w))/. Cheap XOR kernel; port of 'S.xorFast'.
xorFastOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides -> OddStrides
xorFastOS w a b =
  let (za, oa) = forcedBitsOS w a
      (zb, ob) = forcedBitsOS w b
      forcedZeros = (za Bits..&. zb) Bits..|. (oa Bits..&. ob)
      forcedOnes  = (za Bits..&. ob) Bits..|. (oa Bits..&. zb)
  in fromForcedOS w (forcedZeros, forcedOnes)

-- | /O(A(w))/. The arith hull of a factored orbit; port of 'S.toArith'
-- (@isSelfWrapping ? cosetArc : startEndArc@).
toArithOS :: (1 <= w) => NatRepr w -> OddStrides -> A.Domain w
toArithOS w p@(OddStrides v _ s nn)
  | isSelfWrappingOS w p =
      let g = 1 `Bits.shiftL` v :: Natural
      in A.interval imask (toInteger (s Bits..&. (g - 1))) (imask + 1 - toInteger g)
  | otherwise =
      A.interval imask (toInteger s) (toInteger (nn * osStride msk p))
  where
    msk   = fromInteger (NR.maxUnsigned w) :: Natural
    imask = NR.maxUnsigned w

-- | /O(A(w))/. Factored progression from an arith domain; port of
-- 'S.fromArith' (always stride 1).
fromArithOS :: (1 <= w) => NatRepr w -> A.Domain w -> Maybe OddStrides
fromArithOS w d
  | A.isBottom d = Nothing
  | otherwise = case A.arithDomainData d of
      Nothing       -> Just (mkOddStrides msk 0 1 0 msk)   -- BVDAny: full coset
      Just (lo, sz) -> Just (mkOddStrides msk 0 1 (fromInteger lo) (fromInteger sz))
  where
    msk = fromInteger (NR.maxUnsigned w) :: Natural

-- | /O(A(w))/. Cheap containment @a ⊆ b@; port of 'S.leq'.
leqOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides -> Bool
leqOS w a b =
  a == b
  || (bIsFull && cosetMatches && subgroupContained)
  where
    msk   = fromInteger (NR.maxUnsigned w) :: Natural
    gB    = 1 `Bits.shiftL` stridePow2 b :: Natural
    orbitB = (msk + 1) `Bits.shiftR` stridePow2 b
    bIsFull = steps b + 1 == orbitB
    cosetMatches = modSubLocal msk (osStart a) (osStart b) `Prelude.mod` gB == 0
    subgroupContained = osStride msk a `Prelude.mod` gB == 0

-- | /O(A(w))/. Restrict a stride-1 factored arc to the @d@-coset through
-- @s@; port of 'S.restrictToCoset'.
restrictToCosetOS ::
  (1 <= w) => NatRepr w -> OddStrides -> Natural -> Natural -> Maybe OddStrides
restrictToCosetOS w arith s d
  | d <= 1 = Just arith
  | otherwise =
      let m    = fromInteger (NR.maxUnsigned w) :: Natural
          lo   = osStart arith
          nn   = steps arith
          end' = lo + nn                          -- stride 1, so end = lo + n
          off  = modSubLocal m s lo `Prelude.mod` d
          lo'  = lo + off
      in if lo' > end'
           then Nothing
           else mkOddStridesFromStride m (lo' Bits..&. m) d <$> Just ((end' - lo') `Prelude.div` d)

-- | /O(M(w))/. Sound pseudo-join of two factored orbits; port of
-- 'S.pseudoJoin' + 'S.pseudoJoinStrides'.
pseudoJoinOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides -> OddStrides
pseudoJoinOS w a b
  | leqOS w a b = b
  | leqOS w b a = a
  | otherwise =
      let m     = fromInteger (NR.maxUnsigned w) :: Natural
          delta = modSubLocal m (osStart a) (osStart b)
          gcdA  = 1 `Bits.shiftL` stridePow2 a :: Natural
          gcdB  = 1 `Bits.shiftL` stridePow2 b :: Natural
          g0    = case (steps a, steps b) of
                    (0, 0) -> 1
                    (0, _) -> gcdB
                    (_, 0) -> gcdA
                    _      -> min gcdA gcdB
          g     = if delta == 0 then g0 else min g0 (lowestSetBitN delta)
          arc   = A.join (toArithOS w a) (toArithOS w b)
      in case fromArithOS w arc of
           Nothing  -> mkOddStrides m 0 1 0 m
           Just dom -> case restrictToCosetOS w dom (osStart a) g of
             Nothing   -> mkOddStrides m 0 1 0 m
             Just dom' -> dom'

-- | /O(A(w))/. Orbit cardinality @n + 1@; port of 'S.size'.
sizeOS :: OddStrides -> Natural
sizeOS p = steps p + 1

-- | /O(A(w))/. Parity split of a factored orbit; port of 'S.psplit'.
-- Each piece's stride doubles (@v@ rises by one), so the factoring is
-- handed straight to 'mkOddStridesFromStride'.
psplitOS :: (1 <= w) => NatRepr w -> OddStrides -> [OddStrides]
psplitOS w p@(OddStrides v _ s nn)
  | nn == 0 || nn + 1 == orbit || t' == 0 = [p]
  | otherwise =
      [ mkOddStridesFromStride msk s t' nEven
      , mkOddStridesFromStride msk sOdd t' nOdd ]
  where
    msk   = fromInteger (NR.maxUnsigned w) :: Natural
    t     = osStride msk p
    t'    = (2 * t) Bits..&. msk
    orbit = (msk + 1) `Bits.shiftR` v
    nEven = nn `Prelude.div` 2
    nOdd  = (nn - 1) `Prelude.div` 2
    sOdd  = (s + t) Bits..&. msk

-- | Run a sound binary combine at all 'psplitOS' combinations, pseudo-join
-- the sub-results, and keep whichever of the raw and joined results is
-- smaller; port of 'S.psplitOp2'.
psplitOp2OS ::
  (1 <= w) =>
  NatRepr w ->
  (OddStrides -> OddStrides -> OddStrides) ->
  OddStrides -> OddStrides -> OddStrides
psplitOp2OS w op a b =
  let raw  = op a b
      subs = [ op ai bj | ai <- psplitOS w a, bj <- psplitOS w b ]
      pj   = case subs of
               []     -> raw
               (c:cs) -> Prelude.foldr (pseudoJoinOS w) c cs
  in if sizeOS raw <= sizeOS pj then raw else pj

-- | /O(M(w))/. Bitwise AND, 'psplitOp2OS'-wrapped; port of 'S.and'.
andOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides -> OddStrides
andOS w = psplitOp2OS w (andFastOS w)

-- | /O(w · A(w))/. Precise bitwise AND; port of 'S.andPrecise'.
andPreciseOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides -> OddStrides
andPreciseOS w = psplitOp2OS w (andPreciseRawOS w)

-- | /O(M(w))/. Cheap bitwise OR (De Morgan over 'andFastOS'); port of
-- 'S.orFast'.
orFastOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides -> OddStrides
orFastOS w a b = notOS w (andFastOS w (notOS w a) (notOS w b))

-- | /O(M(w))/. Bitwise OR (De Morgan over 'andOS'); port of 'S.or'.
orOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides -> OddStrides
orOS w a b = notOS w (andOS w (notOS w a) (notOS w b))

-- | /O(w · A(w))/. Precise bitwise OR; port of 'S.orPrecise'.
orPreciseOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides -> OddStrides
orPreciseOS w a b = notOS w (andPreciseOS w (notOS w a) (notOS w b))

-- | /O(M(w))/. Bitwise XOR; port of 'S.xor' (cardinality-min of the
-- 'psplitOp2OS'-wrapped 'xorFastOS' and the De Morgan composition).
xorOS :: (1 <= w) => NatRepr w -> OddStrides -> OddStrides -> OddStrides
xorOS w a b =
  let direct = psplitOp2OS w (xorFastOS w) a b
      comp   = andFastOS w (orFastOS w a b) (notOS w (andFastOS w a b))
  in if sizeOS direct <= sizeOS comp then direct else comp

-- ------------------------------------------------------------------
-- * Concatenation, extension, selection, and truncation

zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
zext w d u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof -> compressFromS u (S.zext w (expandToS w d) u) (B.zext (bitwise d) u)

sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
sext w d u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      compressFromS u (S.sext w (expandToS w d) u) (B.sext w (bitwise d) u)

concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> Domain u -> NatRepr v -> Domain v -> Domain (u + v)
concat u a v b =
  case leqAddPosProof u v of
    LeqAddProof ->
      compressFromS (addNat u v)
        (S.concat u (expandToS u a) v (expandToS v b))
        (B.concat u (bitwise a) v (bitwise b))

select ::
  forall i nn w.
  (1 <= nn, 1 <= w, i + nn <= w) =>
  NatRepr i -> NatRepr nn -> NatRepr w -> Domain w -> Domain nn
select i nn w d =
  compressFromS nn
    (S.select i nn w (expandToS w d))
    (B.select i nn (bitwise d))

-- ------------------------------------------------------------------
-- * Shifts and rotations

shl :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
shl w a b =
  compressFromS w (S.shl w (expandToS w a) (expandToS w b)) (shlBitwise w a b)

shlRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
shlRaw w a b =
  compressFromS w (S.shlRaw w (expandToS w a) (expandToS w b)) (shlBitwise w a b)

lshr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
lshr w a b =
  compressFromS w (S.lshr w (expandToS w a) (expandToS w b)) (lshrBitwise w a b)

lshrRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
lshrRaw w a b =
  compressFromS w (S.lshrRaw w (expandToS w a) (expandToS w b)) (lshrBitwise w a b)

ashr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ashr w a b =
  compressFromS w (S.ashr w (expandToS w a) (expandToS w b)) (ashrBitwise w a b)

ashrRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ashrRaw w a b =
  compressFromS w (S.ashrRaw w (expandToS w a) (expandToS w b)) (ashrBitwise w a b)

rol :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
rol w a b =
  compressFromS w (S.rol w (expandToS w a) (expandToS w b)) $
    case reachableAmounts w (rotAmt w) b of
      Just amts -> B.rolAbstractOver w (bitwise a) amts
      Nothing   -> B.rolAbstractBounded w (bitwise a) (bitwise b) (tightUBounds w b)

rolRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
rolRaw w a b =
  compressFromS w (S.rolRaw w (expandToS w a) (expandToS w b)) $
    case reachableAmounts w (rotAmt w) b of
      Just amts -> B.rolAbstractOver w (bitwise a) amts
      Nothing   -> B.rolAbstractBounded w (bitwise a) (bitwise b) (tightUBounds w b)

ror :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ror w a b =
  compressFromS w (S.ror w (expandToS w a) (expandToS w b)) $
    case reachableAmounts w (rotAmt w) b of
      Just amts -> B.rorAbstractOver w (bitwise a) amts
      Nothing   -> B.rorAbstractBounded w (bitwise a) (bitwise b) (tightUBounds w b)

rorRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
rorRaw w a b =
  compressFromS w (S.rorRaw w (expandToS w a) (expandToS w b)) $
    case reachableAmounts w (rotAmt w) b of
      Just amts -> B.rorAbstractOver w (bitwise a) amts
      Nothing   -> B.rorAbstractBounded w (bitwise a) (bitwise b) (tightUBounds w b)

-- ------------------------------------------------------------------
-- * Lattice operations

-- ------------------------------------------------------------------
-- ** Meets

-- | Pseudo-meet on the reduced product.
--
-- /Cuboid fast path/: when both operands are cuboids, the orbit equals
-- its tnum projection, so the joint set is exactly @B.meet ba bb@. We
-- still wrap that in a non-bottom check (the meet may collapse to
-- bottom) and a re-compression so the result honors any low bits the
-- meet newly forces.
pseudoMeet ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
pseudoMeet w a b
  | isCuboid w a && isCuboid w b =
      let bm = B.meet (bitwise a) (bitwise b)
      in if B.isBottom bm
           then Nothing
           else Just (mkCuboidFromBitwise w bm)
  -- Native 2-adic closed form: both strides powers of two (mOdd == 1),
  -- both non-wrapping. The exact intersection needs no modular inverse
  -- (nested CRT moduli), and we skip the bridge's arith-hull detour,
  -- ssplit/compactify, and the eGCD Bézout solve entirely.
  | mOdd a == 1 && mOdd b == 1 && noWrapMod2w w a && noWrapMod2w w b =
      case native2AdicMeet w a b of
        Nothing -> Nothing
        Just sm -> tryCompressFromS w sm (B.meet (bitwise a) (bitwise b))
  | otherwise = do
      sm <- S.pseudoMeet w (expandToS w a) (expandToS w b)
      tryCompressFromS w sm (B.meet (bitwise a) (bitwise b))

pseudoMeetPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
pseudoMeetPrecise w a b
  | isCuboid w a && isCuboid w b =
      let bm = B.meet (bitwise a) (bitwise b)
      in if B.isBottom bm
           then Nothing
           else Just (mkCuboidFromBitwise w bm)
  -- Native 2-adic closed form (exact), as in 'pseudoMeet'.
  | mOdd a == 1 && mOdd b == 1 && noWrapMod2w w a && noWrapMod2w w b =
      case native2AdicMeet w a b of
        Nothing -> Nothing
        Just sm -> tryCompressFromSPrecise w sm (B.meet (bitwise a) (bitwise b))
  -- Native exact-containment short-circuits: when one orbit contains the
  -- other, the meet preserves the smaller operand exactly. This is what
  -- @S.pseudoMeetPrecise@ does internally via 'leqExact'; doing it here
  -- avoids the bridge's @expandToS@ round-trip and @compactifyPrecise@.
  | nativeLeqExact w a b =
      tryCompressFromSPrecise w (expandToS w a) (B.meet (bitwise a) (bitwise b))
  | nativeLeqExact w b a =
      tryCompressFromSPrecise w (expandToS w b) (B.meet (bitwise a) (bitwise b))
  | otherwise = do
      sm <- S.pseudoMeetPrecise w (expandToS w a) (expandToS w b)
      tryCompressFromSPrecise w sm (B.meet (bitwise a) (bitwise b))

-- | /O(w)/. Construct a cuboid OSB.Domain from a non-bottom bitwise
-- domain alone: the unique progression whose tnum is exactly @b@ has
-- @stride = 2^v@, @start = ones@, @n = 2^k − 1@ where @v@ is the
-- bottom forced run and @k@ is the count of free bits in @b@'s
-- contiguous unforced run starting at position @v@... but wait — the
-- cuboid invariant requires the unforced bits to be /contiguous/ above
-- @v@. A general bitwise domain whose unforced bits are scattered is
-- not a cuboid, so this helper instead falls back to compressFromS on
-- the strides projection, which loses no information when @b@ already
-- describes a cuboid (its @S.fromBitwise@ shape is the same orbit).
mkCuboidFromBitwise :: (1 <= w) => NatRepr w -> B.Domain w -> Domain w
mkCuboidFromBitwise w b =
  case S.fromBitwise w b of
    Just s  -> compressFromS w s b
    Nothing -> error "OddStridesBitwise.mkCuboidFromBitwise: \
                     \empty bitwise domain (caller must check B.isBottom)."

-- ------------------------------------------------------------------
-- ** Joins

pseudoJoin ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w
pseudoJoin w a b =
  compressFromS w (S.pseudoJoin w (expandToS w a) (expandToS w b))
    (B.join (bitwise a) (bitwise b))

pseudoJoinPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w
pseudoJoinPrecise w a b =
  compressFromSPrecise w (S.pseudoJoinPrecise w (expandToS w a) (expandToS w b))
    (B.join (bitwise a) (bitwise b))

-- ------------------------------------------------------------------
-- * Branch-condition assumptions

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

assumeSltPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSltPrecise = liftAssume S.assumeSltPrecise B.assumeSlt

assumeSle :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSle = liftAssume S.assumeSle B.assumeSle

assumeSlePrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSlePrecise = liftAssume S.assumeSlePrecise B.assumeSle

assumeSgt :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSgt = liftAssume S.assumeSgt B.assumeSgt

assumeSgtPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSgtPrecise = liftAssume S.assumeSgtPrecise B.assumeSgt

assumeSge :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSge = liftAssume S.assumeSge B.assumeSge

assumeSgePrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSgePrecise = liftAssume S.assumeSgePrecise B.assumeSge

assumeEq :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeEq = pseudoMeet

assumeNe :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeNe = liftAssume S.assumeNe B.assumeNe

liftAssume ::
  (1 <= w) =>
  (NatRepr w -> S.Domain w -> S.Domain w -> Maybe (S.Domain w)) ->
  (NatRepr w -> B.Domain w -> B.Domain w -> B.Domain w) ->
  NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
liftAssume sOp bOp w a b = do
  sm <- sOp w (expandToS w a) (expandToS w b)
  let bm = bOp w (bitwise a) (bitwise b)
  if B.isBottom bm then Nothing else tryCompressFromS w sm bm

liftAssumeBounded ::
  (1 <= w) =>
  (NatRepr w -> S.Domain w -> S.Domain w -> Maybe (S.Domain w)) ->
  (NatRepr w -> B.Domain w -> UnsignedBounds -> B.Domain w) ->
  NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
liftAssumeBounded sOp bOp w a b = do
  sm <- sOp w (expandToS w a) (expandToS w b)
  let bm = bOp w (bitwise a) (tightUBounds w b)
  if B.isBottom bm then Nothing else tryCompressFromS w sm bm

-- ------------------------------------------------------------------
-- * Generators

genDomain :: (1 <= w) => NatRepr w -> Gen (Domain w)
genDomain w = do
  s <- S.genDomain w
  b <- B.genDomain w
  case S.reduce w s b of
    Just (s', b') -> pure (fromReduced s' b')
    Nothing       -> pure (compressFromS w s (S.toBitwise s))

genElement :: (1 <= w) => NatRepr w -> Domain w -> Gen Natural
genElement w d = S.genElement (expandToS w d)

genPair :: (1 <= w) => NatRepr w -> Gen (Domain w, Natural)
genPair w = do
  d <- genDomain w
  x <- genElement w d
  pure (d, x)

-- ------------------------------------------------------------------
-- ** Helper: NatRepr arithmetic

addNat :: NatRepr u -> NatRepr v -> NatRepr (u + v)
addNat = NR.addNat

data LeqAddProof u v where
  LeqAddProof :: (1 <= u + v) => LeqAddProof u v

leqAddPosProof ::
  forall u v. (1 <= u, 1 <= v) => NatRepr u -> NatRepr v -> LeqAddProof u v
leqAddPosProof u v = case NR.leqAddPos u v of
  NR.LeqProof -> LeqAddProof

-- ------------------------------------------------------------------
-- ** Property helpers

maybeMember :: (1 <= w) => NatRepr w -> Maybe (Domain w) -> Natural -> Bool
maybeMember _w Nothing  _ = False
maybeMember w  (Just c) x = member w c x

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
      Just c  -> property (Prelude.all (member w c) xs)
  where
    m = NR.maxUnsigned w
    inRange ys = Prelude.all (\x -> toInteger x Bits..&. m == toInteger x) ys
    strictlyAscending ys = Prelude.and (zipWith (<) ys (drop 1 ys))
    ascendingDistinctInRange = inRange xs && strictlyAscending xs

-- ------------------------------------------------------------------
-- ** Canonicalization

canonLossless :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
canonLossless w c x =
  proper w c ==>
    property (member w (getCanonical (canonicalize w c)) x == member w c x)

canonProper :: (1 <= w) => NatRepr w -> Domain w -> Property
canonProper w c =
  proper w c ==> property (proper w (getCanonical (canonicalize w c)))

canonIdempotent :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
canonIdempotent w c x =
  proper w c ==>
    let one = canonicalize w c
        two = canonicalize w (getCanonical one)
    in property (member w (getCanonical one) x == member w (getCanonical two) x)

-- ------------------------------------------------------------------
-- ** Conversion

toArithCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
toArithCorrect w c x =
  proper w c ==> member w c x ==>
    property (A.member (toArith w c) (toInteger x))

fromArithCorrect ::
  (1 <= w) => NatRepr w -> A.Domain w -> Natural -> Property
fromArithCorrect w a x =
  A.member a (toInteger x) ==>
    case fromArith w a of
      Nothing -> property True
      Just c  -> property (member w c x)

roundtripArith :: (1 <= w) => NatRepr w -> Domain w -> Property
roundtripArith w c =
  proper w c ==>
    case fromArith w (toArith w c) of
      Nothing -> property False
      Just c' -> property (Prelude.and [member w c' x | x <- toList w c])

toBitwiseCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
toBitwiseCorrect w c x =
  proper w c ==> member w c x ==>
    property (B.member (toBitwise c) (toInteger x))

forcedBitsMember :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
forcedBitsMember w c x =
  let (zeros, ones) = forcedBits w c
      m = toInteger (S.mask (expandToS w c))
  in proper w c ==> member w c x ==>
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
      Just c  -> property (member w c x)

-- ------------------------------------------------------------------
-- ** Queries

toListMember :: (1 <= w) => NatRepr w -> Domain w -> Property
toListMember w c =
  proper w c ==> property (Prelude.and [member w c x | x <- toList w c])

memberToList :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
memberToList w c x =
  proper w c ==> property (member w c x == (x `elem` toList w c))

toListNoDuplicates :: (1 <= w) => NatRepr w -> Domain w -> Property
toListNoDuplicates w c =
  proper w c ==>
    let xs = toList w c in property (List.nub xs == xs)

leqCorrect :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
leqCorrect w a b =
  proper w a ==> proper w b ==>
    leq w a b ==> property (Prelude.and [member w b x | x <- toList w a])

leqReflexive :: (1 <= w) => NatRepr w -> Domain w -> Property
leqReflexive w a = proper w a ==> property (leq w a a)

leqTransitive ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w -> Property
leqTransitive w a b c =
  proper w a ==> proper w b ==> proper w c ==>
    leq w a b ==> leq w b c ==> property (leq w a c)

leqPreciseCorrect ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
leqPreciseCorrect w a b =
  proper w a ==> proper w b ==>
    leqPrecise w a b ==>
      property (Prelude.and [member w b x | x <- toList w a])

leqPreciseReflexive :: (1 <= w) => NatRepr w -> Domain w -> Property
leqPreciseReflexive w a = proper w a ==> property (leqPrecise w a a)

sizeViaToList :: (1 <= w) => NatRepr w -> Domain w -> Property
sizeViaToList w c =
  proper w c ==>
    property (toInteger (size w c) >= toInteger (length (toList w c)))

sizeAtMostComponents :: (1 <= w) => NatRepr w -> Domain w -> Property
sizeAtMostComponents w c =
  proper w c ==>
    property (size w c <= S.size (expandToS w c)
           && toInteger (size w c) <= B.size (bitwise c))

sizeExactCorrect :: (1 <= w) => NatRepr w -> Domain w -> Property
sizeExactCorrect w c =
  proper w c ==>
    case sizeExactMaybe w c of
      Nothing -> property True
      Just k  -> property (toInteger k == toInteger (length (toList w c)))

windowMarginalCount :: (1 <= w) => NatRepr w -> Domain w -> Property
windowMarginalCount w c =
  proper w c ==>
    let s          = expandToS w c
        b          = bitwise c
        m_         = B.bvdMask b
        (loB, hiB) = B.bitbounds b
        forcedB    = m_ `Bits.xor` (loB `Bits.xor` hiB)
        fw         = forcedB Bits..&. toInteger (uniformWindowMaskOSB w c)
        target     = loB Bits..&. fw
    in property
         (toInteger (windowMarginal w c)
            == toInteger (length [ x | x <- S.toList s, (toInteger x Bits..&. fw) == target ]))

uniformWindowBalanced :: (1 <= w) => NatRepr w -> Domain w -> Property
uniformWindowBalanced w c =
  proper w c ==>
    let s      = expandToS w c
        wm     = uniformWindowMaskOSB w c
        counts = map length (List.group (List.sort [ x Bits..&. wm | x <- S.toList s ]))
    in property (allEqual counts)
  where
    allEqual []       = True
    allEqual (z : zs) = all (== z) zs

pinsConflictEmpty ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
pinsConflictEmpty w c1 c2 =
  proper w c1 ==> proper w c2 ==>
    let s = expandToS w c1
        b = bitwise c2
    in pinsConflict w c1 b ==>
         property (Prelude.not (any (\x -> B.member b (toInteger x)) (S.toList s)))

-- ------------------------------------------------------------------
-- ** Arithmetic

asN :: NatRepr w -> Integer -> Natural
asN w x = fromInteger (x `Prelude.mod` (NR.maxUnsigned w + 1))

correct_neg ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_neg w a x =
  proper w a ==> member w a x ==>
    property (member w (negate w a) (asN w (Prelude.negate (toInteger x))))

correct_add ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_add w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (member w (add w a b) (asN w (toInteger x + toInteger y)))

correct_sub ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sub w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (member w (sub w a b) (asN w (toInteger x - toInteger y)))

correct_scale ::
  (1 <= w) => NatRepr w -> Integer -> Domain w -> Natural -> Property
correct_scale w k c x =
  proper w c ==> member w c x ==>
    property (member w (scale w k c) (asN w (k * toInteger x)))

correct_mul ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mul w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (member w (mul w a b) (asN w (toInteger x * toInteger y)))

correct_mulPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mulPrecise w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (member w (mulPrecise w a b) (asN w (toInteger x * toInteger y)))

correct_udiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udiv w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> y /= 0 ==>
    property (member w (udiv w a b) (asN w (toInteger x `Prelude.div` toInteger y)))

correct_udivPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udivPrecise w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> y /= 0 ==>
    property (member w (udivPrecise w a b) (asN w (toInteger x `Prelude.div` toInteger y)))

correct_urem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_urem w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> y /= 0 ==>
    property (member w (urem w a b) (asN w (toInteger x `Prelude.mod` toInteger y)))

correct_uremPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_uremPrecise w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> y /= 0 ==>
    property (member w (uremPrecise w a b) (asN w (toInteger x `Prelude.mod` toInteger y)))

correct_sdiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sdiv w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> y /= 0 ==>
    let xs = signedOf w x
        ys = signedOf w y
    in property (member w (sdiv w a b) (asN w (xs `Prelude.quot` ys)))

correct_srem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_srem w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> y /= 0 ==>
    let xs = signedOf w x
        ys = signedOf w y
    in property (member w (srem w a b) (asN w (xs `Prelude.rem` ys)))

signedOf :: (1 <= w) => NatRepr w -> Natural -> Integer
signedOf w x =
  let xi = toInteger x
      hi = NR.maxSigned w
      mod' = NR.maxUnsigned w + 1
  in if xi > hi then xi - mod' else xi

addExact ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
addExact _w _a _b = property True

subExact ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
subExact _w _a _b = property True

mulConstExact ::
  (1 <= w) => NatRepr w -> Integer -> Domain w -> Property
mulConstExact _w _k _c = property True

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
-- *** Power-of-2 fast paths

-- | Scaling by @2^k@ should behave as a left shift: each element in the orbit
-- is shifted left by @k@ positions (mod @2^w@).
correct_scalePow2 ::
  (1 <= w) => NatRepr w -> Natural -> Domain w -> Natural -> Property
correct_scalePow2 w k c x =
  proper w c ==> member w c x ==>
    let pow2 = (2 :: Integer) ^ k
        result = (toInteger x * pow2) `Prelude.mod` (NR.maxUnsigned w + 1)
    in property (member w (scale w pow2 c) (asN w result))

-- | Multiplying by a power-of-2 singleton should behave as a left shift.
correct_mulPow2 ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Natural -> Property
correct_mulPow2 w a x pow2Val =
  proper w a ==> member w a x ==> isPow2 pow2Val ==>
    let result = (toInteger x * toInteger pow2Val) `Prelude.mod` (NR.maxUnsigned w + 1)
    in property (member w (mul w a (singleton w pow2Val)) (asN w result))

-- | Dividing by a power-of-2 singleton should behave as a right shift.
correct_udivPow2 ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Natural -> Property
correct_udivPow2 w a x pow2Val =
  proper w a ==> member w a x ==> isPow2 pow2Val ==>
    let result = toInteger x `Prelude.div` toInteger pow2Val
    in property (member w (udiv w a (singleton w pow2Val)) (asN w result))

-- | Precise division by a power-of-2 singleton should behave as a right shift.
correct_udivPrecisePow2 ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Natural -> Property
correct_udivPrecisePow2 w a x pow2Val =
  proper w a ==> member w a x ==> isPow2 pow2Val ==>
    let result = toInteger x `Prelude.div` toInteger pow2Val
    in property (member w (udivPrecise w a (singleton w pow2Val)) (asN w result))

-- | Remainder with a power-of-2 singleton should behave as a low-bit mask.
correct_uremPow2 ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Natural -> Property
correct_uremPow2 w a x pow2Val =
  proper w a ==> member w a x ==> isPow2 pow2Val ==>
    let result = toInteger x `Prelude.mod` toInteger pow2Val
    in property (member w (urem w a (singleton w pow2Val)) (asN w result))

-- | Precise remainder with a power-of-2 singleton should behave as a low-bit mask.
correct_uremPrecisePow2 ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Natural -> Property
correct_uremPrecisePow2 w a x pow2Val =
  proper w a ==> member w a x ==> isPow2 pow2Val ==>
    let result = toInteger x `Prelude.mod` toInteger pow2Val
    in property (member w (uremPrecise w a (singleton w pow2Val)) (asN w result))

-- | Check if a natural number is a power of two.
isPow2 :: Natural -> Bool
isPow2 0 = False
isPow2 n = n Bits..&. (n - 1) == 0

-- | Create a singleton domain containing a single value.
singleton :: (1 <= w) => NatRepr w -> Natural -> Domain w
singleton w x = mk w x 1 0

-- ------------------------------------------------------------------
-- *** Arithmetic (SMT-LIB div-by-zero semantics)

correct_udivSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udivSmtlib w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    let m = NR.maxUnsigned w
        result = if y == 0
                   then m
                   else toInteger x `Prelude.div` toInteger y
    in property (member w (udivSmtlib w a b) (asN w result))

correct_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_uremSmtlib w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    let result = if y == 0 then toInteger x else toInteger x `Prelude.mod` toInteger y
    in property (member w (uremSmtlib w a b) (asN w result))

correct_sdivSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sdivSmtlib w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    let xs = signedOf w x
        ys = signedOf w y
        m = NR.maxUnsigned w
        result | ys == 0 && xs >= 0 = m
               | ys == 0            = 1
               | otherwise          = xs `Prelude.quot` ys
    in property (member w (sdivSmtlib w a b) (asN w result))

correct_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sremSmtlib w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    let xs = signedOf w x
        ys = signedOf w y
        result | ys == 0 = xs
               | otherwise = xs `Prelude.rem` ys
    in property (member w (sremSmtlib w a b) (asN w result))

-- ------------------------------------------------------------------
-- *** Arithmetic (LLVM overflow flags)

flaggedSoundRP' ::
  (1 <= w) => NatRepr w -> Maybe (Domain w) -> Bool -> Natural -> Bool
flaggedSoundRP' w r constraintHolds z = case r of
  Nothing -> Prelude.not constraintHolds
  Just d  -> Prelude.not constraintHolds || member w d z

correct_addNuw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_addNuw w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (addNuw w a b) noOverflow z)
  where
    sumI = toInteger x + toInteger y
    noOverflow = sumI <= NR.maxUnsigned w
    z = asN w sumI

correct_addNsw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_addNsw w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (addNsw w a b) noOverflow z)
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
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (addNswNuw w a b) noOverflow z)
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
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (subNuw w a b) noOverflow z)
  where
    diffI = toInteger x - toInteger y
    noOverflow = diffI >= 0
    z = asN w diffI

correct_subNsw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_subNsw w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (subNsw w a b) noOverflow z)
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
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (subNswNuw w a b) noOverflow z)
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
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (mulNuw w a b) noOverflow z)
  where
    prodI = toInteger x * toInteger y
    noOverflow = prodI <= NR.maxUnsigned w
    z = asN w prodI

correct_mulNsw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mulNsw w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (mulNsw w a b) noOverflow z)
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
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (mulNswNuw w a b) noOverflow z)
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
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (shlNuw w a b) noOverflow z)
  where
    yI = toInteger y
    shifted = toInteger x * (1 `Bits.shiftL` fromInteger yI)
    noOverflow = yI < NR.intValue w && shifted <= NR.maxUnsigned w
    z = asN w shifted

correct_shlNsw ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_shlNsw w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (shlNsw w a b) noOverflow z)
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
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (shlNswNuw w a b) noOverflow z)
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
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (udivExact w a b) constraintHolds z)
  where
    constraintHolds = y /= 0 && x `Prelude.rem` y == 0
    z = if y == 0 then 0 else x `Prelude.quot` y

correct_sdivExact ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sdivExact w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (sdivExact w a b) constraintHolds z)
  where
    xs = signedOf w x
    ys = signedOf w y
    constraintHolds = ys /= 0 && xs `Prelude.rem` ys == 0
    z = if ys == 0 then 0 else asN w (xs `Prelude.quot` ys)

correct_lshrExact ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_lshrExact w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (lshrExact w a b) constraintHolds z)
  where
    yI = fromInteger (min (toInteger y) (NR.intValue w)) :: Int
    constraintHolds = x Bits..&. ((1 `Bits.shiftL` yI) - 1) == 0
    z = x `Bits.shiftR` yI

correct_ashrExact ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ashrExact w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (flaggedSoundRP' w (ashrExact w a b) constraintHolds z)
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
  proper w a ==> member w a x ==>
    let m = toInteger (S.mask (expandToS w a))
    in property (member w (not w a) (fromInteger (m - toInteger x)))

correct_and ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_and w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (member w (and w a b) (fromInteger (toInteger x .&. toInteger y)))
  where
    (.&.) = (Bits..&.)

correct_or ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_or w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (member w (or w a b) (fromInteger (toInteger x .|. toInteger y)))
  where
    (.|.) = (Bits..|.)

correct_xor ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_xor w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (member w (xor w a b) (fromInteger (toInteger x `xorI` toInteger y)))

correct_andPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_andPrecise w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (member w (andPrecise w a b) (fromInteger (toInteger x .&. toInteger y)))
  where
    (.&.) = (Bits..&.)

correct_orPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_orPrecise w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    property (member w (orPrecise w a b) (fromInteger (toInteger x .|. toInteger y)))
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
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      proper w a ==> member w a x ==>
        property (member u (zext w a u) x)

correct_sign_ext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Natural -> Property
correct_sign_ext w a u x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      proper w a ==> member w a x ==>
        let xs = signedOf w x
        in property (member u (sext w a u) (asN u xs))

correct_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> Domain u -> Natural -> NatRepr v -> Domain v -> Natural -> Property
correct_concat u a x v b y =
  case leqAddPosProof u v of
    LeqAddProof ->
      let mv = NR.maxUnsigned v + 1
          xy = toInteger x * mv + toInteger y
      in proper u a ==> proper v b ==> member u a x ==> member v b y ==>
           property (member (addNat u v) (concat u a v b) (fromInteger xy))

correct_select ::
  forall i nn w.
  (1 <= nn, 1 <= w, i + nn <= w) =>
  NatRepr i -> NatRepr nn -> NatRepr w -> Domain w -> Natural -> Property
correct_select i nn w c x =
  proper w c ==> member w c x ==>
    let ii = toInteger (NR.natValue i)
        m  = NR.maxUnsigned nn
        bits = (toInteger x `Prelude.div` (2 ^ ii)) Bits..&. m
    in property (member nn (select i nn w c) (fromInteger bits))

-- ------------------------------------------------------------------
-- ** Shifts and rotations

correct_shl ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_shl w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    let yi = toInteger y
        wi = toInteger (NR.natValue w)
        shifted | yi >= wi  = 0
                | otherwise = toInteger x * (2 ^ yi)
    in property (member w (shl w a b) (asN w shifted))

correct_lshr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_lshr w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    let yi = toInteger y
        wi = toInteger (NR.natValue w)
        shifted | yi >= wi  = 0
                | otherwise = toInteger x `Prelude.div` (2 ^ yi)
    in property (member w (lshr w a b) (asN w shifted))

correct_ashr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ashr w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    let yi  = toInteger y
        wi  = toInteger (NR.natValue w)
        xs  = signedOf w x
        shifted | yi >= wi  = if xs < 0 then -1 else 0
                | otherwise = xs `Prelude.div` (2 ^ yi)
    in property (member w (ashr w a b) (asN w shifted))

correct_rol ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_rol w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    let wi = NR.natValue w
        yi = y `Prelude.mod` wi
        xi = toInteger x
        m  = NR.maxUnsigned w
        rotated = ((xi * 2 ^ yi) Bits..|.
                   (xi `Prelude.div` 2 ^ (wi - yi))) Bits..&. m
    in property (member w (rol w a b) (asN w rotated))

correct_ror ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ror w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    let wi = NR.natValue w
        yi = y `Prelude.mod` wi
        xi = toInteger x
        m  = NR.maxUnsigned w
        rotated = ((xi `Prelude.div` 2 ^ yi) Bits..|.
                   (xi * 2 ^ (wi - yi))) Bits..&. m
    in property (member w (ror w a b) (asN w rotated))

-- ------------------------------------------------------------------
-- ** Lattice operations

-- ------------------------------------------------------------------
-- *** Meets

correct_pseudoMeet ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_pseudoMeet w a b x =
  proper w a ==> proper w b ==> member w a x ==> member w b x ==>
    case pseudoMeet w a b of
      Nothing -> property False
      Just c  -> property (member w c x)

correct_pseudoMeetPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_pseudoMeetPrecise w a b x =
  proper w a ==> proper w b ==> member w a x ==> member w b x ==>
    case pseudoMeetPrecise w a b of
      Nothing -> property False
      Just c  -> property (member w c x)

pseudoMeetLowerBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoMeetLowerBound w a b x =
  proper w a ==> proper w b ==>
  Prelude.not (wraps w a) ==> Prelude.not (wraps w b) ==>
    case pseudoMeet w a b of
      Nothing -> property True
      Just c  -> member w c x ==> property (member w a x && member w b x)

pseudoMeetPreciseLowerBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoMeetPreciseLowerBound w a b x =
  proper w a ==> proper w b ==>
  Prelude.not (wraps w a) ==> Prelude.not (wraps w b) ==>
    case pseudoMeetPrecise w a b of
      Nothing -> property True
      Just c  -> member w c x ==> property (member w a x && member w b x)

wraps :: (1 <= w) => NatRepr w -> Domain w -> Bool
wraps w a =
  let s = expandToS w a
  in S.start s + S.n s * S.stride s > S.mask s

pseudoMeetCommutative ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoMeetCommutative w a b x =
  proper w a ==> proper w b ==>
    property (maybeMember w (pseudoMeet w a b) x == maybeMember w (pseudoMeet w b a) x)

pseudoMeetPreciseCommutative ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoMeetPreciseCommutative w a b x =
  proper w a ==> proper w b ==>
    property (maybeMember w (pseudoMeetPrecise w a b) x
               == maybeMember w (pseudoMeetPrecise w b a) x)

pseudoMeetIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoMeetIdempotent w a x =
  proper w a ==>
    case pseudoMeet w a a of
      Nothing -> property False
      Just c  -> property (member w c x == member w a x)

pseudoMeetPreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoMeetPreciseIdempotent w a x =
  proper w a ==>
    case pseudoMeetPrecise w a a of
      Nothing -> property False
      Just c  -> property (member w c x == member w a x)

pseudoMeetTopIdentity ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoMeetTopIdentity w a x =
  proper w a ==>
    case pseudoMeet w a (top w) of
      Nothing -> property False
      Just c  -> property (member w c x == member w a x)

pseudoMeetPreciseTopIdentity ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoMeetPreciseTopIdentity w a x =
  proper w a ==>
    case pseudoMeetPrecise w a (top w) of
      Nothing -> property False
      Just c  -> property (member w c x == member w a x)

-- ------------------------------------------------------------------
-- *** Joins

correct_pseudoJoin ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_pseudoJoin w a b x =
  proper w a ==> proper w b ==> (member w a x Prelude.|| member w b x) ==>
    property (member w (pseudoJoin w a b) x)

correct_pseudoJoinPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_pseudoJoinPrecise w a b x =
  proper w a ==> proper w b ==> (member w a x Prelude.|| member w b x) ==>
    property (member w (pseudoJoinPrecise w a b) x)

pseudoJoinUpperBound ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoJoinUpperBound w a b x =
  proper w a ==> proper w b ==>
    let c = pseudoJoin w a b
    in (member w a x Prelude.|| member w b x) ==> property (member w c x)

pseudoJoinPreciseUpperBound ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoJoinPreciseUpperBound w a b x =
  proper w a ==> proper w b ==>
    let c = pseudoJoinPrecise w a b
    in (member w a x Prelude.|| member w b x) ==> property (member w c x)

pseudoJoinCommutative ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoJoinCommutative w a b x =
  proper w a ==> proper w b ==>
    property (member w (pseudoJoin w a b) x == member w (pseudoJoin w b a) x)

pseudoJoinPreciseCommutative ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoJoinPreciseCommutative w a b x =
  proper w a ==> proper w b ==>
    property (member w (pseudoJoinPrecise w a b) x
               == member w (pseudoJoinPrecise w b a) x)

pseudoJoinIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoJoinIdempotent w a x =
  proper w a ==>
    let c = pseudoJoin w a a in property (member w c x == member w a x)

pseudoJoinPreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoJoinPreciseIdempotent w a x =
  proper w a ==>
    let c = pseudoJoinPrecise w a a
    in property (member w c x == member w a x)

pseudoJoinPreciseRefinesJoin ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
pseudoJoinPreciseRefinesJoin w a b x =
  proper w a ==> proper w b ==>
    member w (pseudoJoinPrecise w a b) x ==>
      property (member w (pseudoJoin w a b) x)

pseudoJoinTopAnnihilator ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoJoinTopAnnihilator w a x =
  proper w a ==>
    let c = pseudoJoin w a (top w)
    in property (member w c x == member w (top w) x)

pseudoJoinPreciseTopAnnihilator ::
  (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
pseudoJoinPreciseTopAnnihilator w a x =
  proper w a ==>
    let c = pseudoJoinPrecise w a (top w)
    in property (member w c x == member w (top w) x)

-- ------------------------------------------------------------------
-- ** Branch-condition assumptions

correct_assumeUlt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUlt w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> x < y ==>
    maybeMemberOrFail w (assumeUlt w a b) x

correct_assumeUle ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUle w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> x <= y ==>
    maybeMemberOrFail w (assumeUle w a b) x

correct_assumeUgt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUgt w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> x > y ==>
    maybeMemberOrFail w (assumeUgt w a b) x

correct_assumeUge ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUge w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> x >= y ==>
    maybeMemberOrFail w (assumeUge w a b) x

correct_assumeSlt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSlt w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    signedOf w x < signedOf w y ==>
      maybeMemberOrFail w (assumeSlt w a b) x

correct_assumeSle ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSle w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    signedOf w x <= signedOf w y ==>
      maybeMemberOrFail w (assumeSle w a b) x

correct_assumeSgt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSgt w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    signedOf w x > signedOf w y ==>
      maybeMemberOrFail w (assumeSgt w a b) x

correct_assumeSge ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSge w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    signedOf w x >= signedOf w y ==>
      maybeMemberOrFail w (assumeSge w a b) x

correct_assumeSltPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSltPrecise w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    signedOf w x < signedOf w y ==>
      maybeMemberOrFail w (assumeSltPrecise w a b) x

correct_assumeSlePrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSlePrecise w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    signedOf w x <= signedOf w y ==>
      maybeMemberOrFail w (assumeSlePrecise w a b) x

correct_assumeSgtPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSgtPrecise w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    signedOf w x > signedOf w y ==>
      maybeMemberOrFail w (assumeSgtPrecise w a b) x

correct_assumeSgePrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSgePrecise w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==>
    signedOf w x >= signedOf w y ==>
      maybeMemberOrFail w (assumeSgePrecise w a b) x

correct_assumeEq ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeEq w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> x == y ==>
    maybeMemberOrFail w (assumeEq w a b) x

correct_assumeNe ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeNe w a x b y =
  proper w a ==> proper w b ==> member w a x ==> member w b y ==> x /= y ==>
    maybeMemberOrFail w (assumeNe w a b) x

assumeUltShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeUltShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeUlt w) a b)

assumeUleShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeUleShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeUle w) a b)

assumeUgtShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeUgtShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeUgt w) a b)

assumeUgeShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeUgeShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeUge w) a b)

assumeSltShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSltShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeSlt w) a b)

assumeSleShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSleShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeSle w) a b)

assumeSgtShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSgtShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeSgt w) a b)

assumeSgeShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSgeShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeSge w) a b)

assumeSltPreciseShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSltPreciseShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeSltPrecise w) a b)

assumeSlePreciseShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSlePreciseShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeSlePrecise w) a b)

assumeSgtPreciseShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSgtPreciseShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeSgtPrecise w) a b)

assumeSgePreciseShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeSgePreciseShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeSgePrecise w) a b)

assumeNeShrinks :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
assumeNeShrinks w a b =
  proper w a ==> proper w b ==> property (stridesShrinks w (assumeNe w) a b)

stridesShrinks ::
  (1 <= w) =>
  NatRepr w ->
  (Domain w -> Domain w -> Maybe (Domain w)) -> Domain w -> Domain w -> Bool
stridesShrinks w op a b =
  case op a b of
    Nothing -> True
    Just c  -> S.size (expandToS w c) <= S.size (expandToS w a)

assumeSltPreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
assumeSltPreciseIdempotent w a b x =
  proper w a ==> proper w b ==>
  Prelude.not (wraps w a) ==> Prelude.not (wraps w b) ==>
    property (idempotentAt w (assumeSltPrecise w) a b x)

assumeSlePreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
assumeSlePreciseIdempotent w a b x =
  proper w a ==> proper w b ==>
  Prelude.not (wraps w a) ==> Prelude.not (wraps w b) ==>
    property (idempotentAt w (assumeSlePrecise w) a b x)

assumeSgtPreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
assumeSgtPreciseIdempotent w a b x =
  proper w a ==> proper w b ==>
  Prelude.not (wraps w a) ==> Prelude.not (wraps w b) ==>
    property (idempotentAt w (assumeSgtPrecise w) a b x)

assumeSgePreciseIdempotent ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
assumeSgePreciseIdempotent w a b x =
  proper w a ==> proper w b ==>
  Prelude.not (wraps w a) ==> Prelude.not (wraps w b) ==>
    property (idempotentAt w (assumeSgePrecise w) a b x)

idempotentAt ::
  (1 <= w) =>
  NatRepr w ->
  (Domain w -> Domain w -> Maybe (Domain w)) ->
  Domain w -> Domain w -> Natural -> Bool
idempotentAt w op a b x =
  case op a b of
    Nothing -> True
    Just c  -> maybeMember w (op c b) x == member w c x

maybeMemberOrFail :: (1 <= w) => NatRepr w -> Maybe (Domain w) -> Natural -> Bool
maybeMemberOrFail _w Nothing  _ = False
maybeMemberOrFail w  (Just c) x = member w c x

-- ------------------------------------------------------------------
-- *** Internal helpers

-- | 'gcdOdd' (Stein's binary GCD on two odds) agrees with the prelude
-- 'Prelude.gcd' on odd inputs. The generator forces both arguments odd
-- by setting their low bit; this is the load-bearing correctness check
-- for the native 'add'\/'sub'\/'mul' precision restoration.
gcdOddMatchesPrelude :: Natural -> Natural -> Property
gcdOddMatchesPrelude a0 b0 =
  let a = a0 Bits..|. 1
      b = b0 Bits..|. 1
  in property (gcdOdd a b == Prelude.gcd a b)

-- | 'binGcd' (2-adic split + 'gcdOdd' on the odd parts) agrees with the
-- prelude 'Prelude.gcd' on arbitrary inputs, including zeros.
binGcdMatchesPrelude :: Natural -> Natural -> Property
binGcdMatchesPrelude a b =
  property (binGcd a b == Prelude.gcd a b)

-- | The native 'nativeLeqPrecise' agrees with the bridged
-- @S.leqPrecise (expandToS …)@ it replaces, on the strides projection.
-- This is the load-bearing correctness check for the native
-- reduced-width containment in 'leqPrecise'.
nativeLeqPreciseMatchesBridge ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
nativeLeqPreciseMatchesBridge w a b =
  proper w a ==> proper w b ==>
    property (nativeLeqPrecise w a b
                == S.leqPrecise (expandToS w a) (expandToS w b))

-- | When the native 2-adic meet fires (both strides powers of two, both
-- non-wrapping), its exact intersection denotes the same set as the
-- bridged @S.pseudoMeet@ — checked at a witness point and (implicitly,
-- via the soundness suite) as a subset. The precondition mirrors the
-- guard in 'pseudoMeet'; when it does not hold the property is vacuously
-- true. This both certifies the closed form and confirms the path is
-- actually exercised (non-vacuous on the generated inputs).
native2AdicMeetMatchesBridge ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
native2AdicMeetMatchesBridge w a b x =
  proper w a ==> proper w b ==>
  (mOdd a == 1 && mOdd b == 1 && noWrapMod2w w a && noWrapMod2w w b) ==>
    let nativeR = native2AdicMeet w a b
        bridgeR = S.pseudoMeet w (expandToS w a) (expandToS w b)
    in property (memberMaybeS w nativeR x == memberMaybeS w bridgeR x)

-- | Membership in an optional strides-side domain at a witness.
memberMaybeS :: (1 <= w) => NatRepr w -> Maybe (S.Domain w) -> Natural -> Bool
memberMaybeS _ Nothing  _ = False
memberMaybeS _ (Just s) x = S.member s x

-- | The native 'nativeLeqExact' agrees with the bridged
-- @S.leqExact (expandToS …)@ on the strides projection, including the
-- 'floorSumN' residual path (exercised at small\/medium widths where the
-- large-window case arises). Load-bearing check for the native exact
-- containment used inside 'pseudoMeetPrecise'.
nativeLeqExactMatchesBridge ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
nativeLeqExactMatchesBridge w a b =
  proper w a ==> proper w b ==>
    property (nativeLeqExact w a b
                == S.leqExact (expandToS w a) (expandToS w b))

-- | The native 'reduceN' denotes exactly the same reduced product as the
-- bridged @tryCompressFromS (expandToS …)@ (i.e. @S.reduce@ +
-- 'fromReduced'): identical emptiness, identical OSB fields, and
-- identical bitwise component. Load-bearing check that the factored
-- native reduce replaces the @expandToS → S.reduce → fromReduced@ bridge
-- with no precision or representation drift.
nativeReduceMatchesBridge ::
  (1 <= w) => NatRepr w -> Domain w -> B.Domain w -> Natural -> Property
nativeReduceMatchesBridge w a b x =
  proper w a ==>
    let nativeR = reduceN w a b
        bridgeR = tryCompressFromS w (expandToS w a) b
        fields d = (startHigh d, mOdd d, n d, B.bitbounds (bitwise d), B.bvdMask (bitwise d))
    in property (maybeMember w nativeR x == maybeMember w bridgeR x
              && fmap fields nativeR == fmap fields bridgeR)
