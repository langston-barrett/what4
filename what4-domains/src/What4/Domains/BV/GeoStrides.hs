{-|
Module      : What4.Domains.BV.GeoStrides
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Geometric strides are an abstract domain for the /multiplicative/ structure of
bitvectors, the orthogonal partner to "What4.Domains.BV.Strides" (which captures
the additive group @(ℤ\/2^w, +)@). Where strides is blind to multiplicative
induction — @x <<= 1@ produces @{1,2,4,8,…}@, on which strides reports top — geo
strides is exact, because such sequences are arithmetic progressions in
/log-space/.

This module is the /kernel/: it represents nonempty sets of /nonzero/ bitvectors
only. The lattice-completed domain (adding the empty set, @{0}@, and their
combinations) is "What4.Domains.BV.Geometric", which wraps this kernel the way
"What4.Domains.BV.StridedInterval" wraps "What4.Domains.BV.Strides". The split is
forced by the ring structure: multiplication has zero divisors (e.g.
@2·8 ≡ 0 (mod 16)@), so a product of nonzero values can be @0@, which has no
logarithm and cannot be represented in the kernel.

== The factorization

The unit group factors as @U(ℤ\/2^w) ≅ ℤ\/2 × ℤ\/2^{w-2}@ for @w ≥ 3@, with
@⟨5⟩@ the cyclic part (it reaches exactly the residues @≡ 1 (mod 4)@) and @⟨-1⟩@
the @ℤ\/2@ factor. Combined with peeling off powers of two, every /nonzero/ @x@
factors uniquely as

@
x = 2^v · (-1)^κ · 5^k  (mod 2^w)
@

where @v = ctz(x) ∈ [0, w)@, @κ ∈ {0,1}@ is the mod-4 class of the odd part
@x >> v@, and @k ∈ [0, 2^{w-2})@ is the base-5 discrete logarithm of that odd
part (after folding the @≡ 3 (mod 4)@ case into the @≡ 1 (mod 4)@ coset via the
@(-1)@ factor). A kernel element stores a 'S.Domain'-valued /set/ of each
coordinate: the valuation 'trailingZeroes', the mod-4 class 'oddClass', and the
discrete log 'log5Odd'.

Because exponents add under multiplication, @mul@ becomes 'S.add' on
'trailingZeroes' and 'log5Odd' (and an exclusive-or on 'oddClass'); @square@ and
@pow@ become 'S.scale'. The 'log5Odd' axis lives at width @w-2@, so its strides
arithmetic already wraps modulo @2^{w-2}@ exactly.
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Domains.BV.GeoStrides
  ( -- * 2-adic discrete log
    pow5
  , dlog5
  , OddClass(..)
  , decompose
  , recompose
    -- * Construction
  , Domain
  , trailingZeroes
  , oddClass
  , log5Odd
  , proper
  , mk
  , top
    -- * Queries
  , member
  , toList
  , size
  , leq
    -- * Arithmetic
  , one
  , negate
  , mul
  , square
  , pow
  , shl
  , mayBeZero
    -- * Lattice operations
    -- ** Joins
  , pseudoJoin
    -- ** Meets
  , pseudoMeet
    -- * Generators
  , genDomain
  , genElement
  , genPair
    -- * Properties
    -- ** 2-adic discrete log
  , dlog5Pow5RoundTrip
  , pow5Dlog5RoundTrip
  , decomposeRecomposeRoundTrip
  , pow5Multiplicative
    -- ** Queries
  , memberToList
  , toListMember
  , toListNoDuplicates
  , sizeViaToList
    -- ** Arithmetic
  , correct_neg
  , correct_mul
  , correct_square
  , correct_pow
    -- ** Lattice
  , correct_pseudoJoin
  , correct_pseudoMeet
  , leqReflexive
  , leqTransitive
  , oddClassJoinAssoc
  , oddClassMeetAssoc
  ) where

import           Control.Exception (assert)
import           Data.Bits ((.&.), shiftL, shiftR)
import qualified Data.Bits as Bits
import qualified Data.List as List
import qualified Data.Set as Set
import           GHC.TypeNats (Nat, type (-), type (<=))
import           Numeric.Natural (Natural)
import           Prelude hiding (negate)

import           Data.Parameterized.NatRepr (NatRepr, LeqProof(..), knownNat)
import qualified Data.Parameterized.NatRepr as NR

import           What4.Domains.Arithmetic (countTrailingZerosOr0, log2OfPowerOfTwo)
import qualified What4.Domains.BV.Strides as S
import           What4.Domains.Verification (Property, property, (==>), Gen, chooseInt)

-- ------------------------------------------------------------------
-- * 2-adic discrete log
--
-- These helpers operate on raw 'Natural's modulo @m = 2^w@ (so all reduction is
-- @.&. (m-1)@) and underlie 'decompose' \/ 'recompose'. They mirror the Hensel
-- lifting style of 'S.invModPow2'.

-- | @pow5 m k = 5^k mod m@, for @m@ a power of two. Computed by
-- square-and-multiply.
pow5 :: Natural -> Natural -> Natural
pow5 m = go 1 (5 .&. mMinus1)
  where
    mMinus1 = m - 1
    go acc _    0 = acc
    go acc base e =
      let !acc' = if e .&. 1 == 1 then (acc * base) .&. mMinus1 else acc
      in go acc' ((base * base) .&. mMinus1) (e `shiftR` 1)

-- | @dlog5 m u@ is the base-5 discrete logarithm of @u@ modulo @m = 2^w@: the
-- unique @k ∈ [0, 2^{w-2})@ with @5^k ≡ u (mod m)@. Defined only for @u@ odd
-- with @u ≡ 1 (mod 4)@.
--
-- Computed by a bit-by-bit Hensel lift. The key fact is
-- @5^{2^j} ≡ 1 + 2^{j+2} (mod 2^{j+3})@, so toggling exponent-bit @j@ flips
-- residue-bit @j+2@ and nothing lower: at round @j@ we have @5^k ≡ u
-- (mod 2^{j+2})@ and we set bit @j@ of @k@ exactly when the bits disagree at
-- position @j+2@.
dlog5 :: Natural -> Natural -> Natural
dlog5 m u =
  assert (u .&. 3 == 1) $
  go 0 0 1 (5 .&. mMinus1)
  where
    mMinus1 = m - 1
    -- @w-2@ exponent bits, where @m = 2^w@.
    nbits = max 0 (popHigh m - 2)
    go !j !k !p !fivePow
      | j >= nbits = k
      | otherwise =
          let modHi = (1 `shiftL` (j + 3)) - 1
          in if (p .&. modHi) == (u .&. modHi)
               then go (j + 1) k p ((fivePow * fivePow) .&. mMinus1)
               else go (j + 1) (k + (1 `shiftL` j))
                       ((p * fivePow) .&. mMinus1)
                       ((fivePow * fivePow) .&. mMinus1)

-- | The position of the single set bit of a power of two: @popHigh (2^w) = w@.
popHigh :: Natural -> Int
popHigh x = log2OfPowerOfTwo (toInteger x)

-- | The mod-4 class of a nonzero value's odd part: the forced @ℤ\/2@ coordinate
-- of the factorization (the @(-1)^κ@ factor). 'OddClassTop' is the join of the
-- two classes (\"either\"), used when a kernel element's odd parts span both.
data OddClass
  = OneMod4       -- ^ odd part @≡ 1 (mod 4)@ (@κ = 0@)
  | ThreeMod4     -- ^ odd part @≡ 3 (mod 4)@ (@κ = 1@)
  | OddClassTop   -- ^ either class
  deriving (Eq, Ord, Show)

-- | Decompose a bitvector into its multiplicative coordinates
-- @(v, oddClass, k)@, or 'Nothing' for @0@ (which has no logarithm). Requires
-- @w ≥ 3@.
decompose ::
  (3 <= w) =>
  NatRepr w -> Natural -> Maybe (Natural, OddClass, Natural)
decompose w x0
  | x == 0 = Nothing
  | otherwise = Just (v, oc, k)
  where
    m = modulus w
    mMinus1 = m - 1
    x = x0 .&. mMinus1
    v = fromIntegral (lowBit x)
    odd' = x `shiftR` fromIntegral v
    (oc, u) = if odd' .&. 2 == 0
                then (OneMod4, odd')
                else (ThreeMod4, (m - odd') .&. mMinus1)
    k = dlog5 m u

-- | Recompose multiplicative coordinates @(v, oddClass, k)@ back into a
-- bitvector: @2^v · (-1)^κ · 5^k (mod 2^w)@. The inverse of 'decompose' on
-- nonzero values. Requires @w ≥ 3@. 'OddClassTop' is treated as 'OneMod4'
-- (it is not a concrete coordinate).
recompose ::
  (3 <= w) =>
  NatRepr w -> Natural -> OddClass -> Natural -> Natural
recompose w v oc k = (oddPart `shiftL` fromIntegral v) .&. mMinus1
  where
    m = modulus w
    mMinus1 = m - 1
    fivePow = pow5 m k
    oddPart = case oc of
      ThreeMod4 -> (m - fivePow) .&. mMinus1
      _         -> fivePow

-- | The index of the lowest set bit (i.e. @ctz@) of a nonzero 'Natural'.
lowBit :: Natural -> Int
lowBit x = countTrailingZerosOr0 (toInteger x)

-- ------------------------------------------------------------------
-- * Construction

-- | A kernel geometric-strides element at width @w@: a nonempty set of
-- /nonzero/ bitvectors, stored as a set of each multiplicative coordinate. The
-- 'log5Odd' component lives at width @w-2@, so its arithmetic is exactly modulo
-- @2^{w-2}@.
data Domain (w :: Nat)
  = Domain
    { trailingZeroes :: !(S.Domain w)
      -- ^ The set of valuations @v = ctz(x)@. Members lie in @[0, w)@.
    , oddClass :: !OddClass
      -- ^ The mod-4 class of the odd part @x >> v@.
    , log5Odd :: !(S.Domain (w - 2))
      -- ^ The set of base-5 discrete logs @k@ of the odd part, in @ℤ\/2^{w-2}@.
    }
  deriving (Eq, Ord, Show)

-- | The data-structure invariants of a kernel 'Domain': both coordinate axes
-- are 'S.proper', and every valuation lies in @[0, w)@ (so the represented set
-- is nonzero).
proper :: (3 <= w) => NatRepr w -> Domain w -> Bool
proper w (Domain tz _ lo) =
  S.proper tz
  && S.proper lo
  && Prelude.all (< NR.natValue w) (S.toList tz)

-- | From @3 <= w@, produce the @w-2@ width repr and the evidence @1 <= w-2@
-- that the 'log5Odd' axis's strides operations require.
geoWidth ::
  forall w.
  (3 <= w) =>
  NatRepr w ->
  (NatRepr (w - 2), LeqProof 1 (w - 2))
geoWidth w = (wMinus2, posProof)
  where
    le2w :: LeqProof 2 w
    le2w = NR.leqTrans (LeqProof :: LeqProof 2 3) (LeqProof :: LeqProof 3 w)

    wMinus2 :: NatRepr (w - 2)
    wMinus2 = NR.withLeqProof le2w (NR.subNat w (knownNat @2))

    -- @leqSub2 (3 <= w) (2 <= 2) :: LeqProof (3-2) (w-2) = LeqProof 1 (w-2)@.
    posProof :: LeqProof 1 (w - 2)
    posProof = NR.leqSub2 (LeqProof :: LeqProof 3 w) (LeqProof :: LeqProof 2 2)

-- | @modulus w = 2^w@.
modulus :: NatRepr w -> Natural
modulus w = 1 `shiftL` NR.widthVal w

-- | Evidence @1 <= w@ derived from @3 <= w@, for the full-width 'S.Domain'
-- operations on the 'trailingZeroes' axis.
oneLeqW :: forall w. (3 <= w) => NatRepr w -> LeqProof 1 w
oneLeqW _ = NR.leqTrans (LeqProof :: LeqProof 1 3) (LeqProof :: LeqProof 3 w)

-- | Construct a kernel element from coordinate-axis sets. Asserts the
-- 'proper' invariants.
mk ::
  (3 <= w) =>
  NatRepr w ->
  S.Domain w ->
  OddClass ->
  S.Domain (w - 2) ->
  Domain w
mk w tz oc lo =
  assert (S.proper tz) $
  assert (S.proper lo) $
  let c = Domain tz oc lo
  in assert (proper w c) c

-- | The top element of the kernel lattice: /all/ nonzero bitvectors. The
-- valuation ranges over @[0, w-1]@, the odd class is either, and the discrete
-- log ranges over all of @ℤ\/2^{w-2}@.
top :: (3 <= w) => NatRepr w -> Domain w
top w =
  case geoWidth w of
    (w2, LeqProof) ->
      -- Valuations @[0, w-1]@: start 0, stride 1, @w-1@ steps.
      mk w (S.mk w 0 1 (NR.natValue w - 1)) OddClassTop (S.top w2)

-- ------------------------------------------------------------------
-- * Queries

-- | Test whether a value is a member of the represented set. @0@ is never a
-- member (the kernel holds only nonzero values).
--
-- This is exact and runs in polynomial time (no enumeration of the
-- concretization). The valuation @v = ctz(x)@ is /forced/ (the odd part is
-- always odd), so it must be a member of 'trailingZeroes'. The odd-part class
-- is then checked against 'oddClass', and the discrete-log constraint reduces
-- to a coset intersection on 'log5Odd': because @2^v · 5^k (mod 2^w)@ depends
-- only on @5^k (mod 2^{w-v})@, i.e. on @k (mod 2^{w-v-2})@, @x@ is a member iff
-- 'log5Odd' contains /some/ @k@ congruent to the value's log modulo
-- @2^{w-v-2}@.
member :: (3 <= w) => NatRepr w -> Domain w -> Natural -> Bool
member w (Domain tz oc lo) x
  | x == 0 = False
  | not (S.member tz (fromIntegral v)) = False
  | r == 1 = True            -- @2^{w-1} · odd ≡ 2^{w-1}@ for every odd part
  | not (oddClassMember oc kClass) = False
  | r == 2 = True            -- @k@ is unconstrained modulo @2^0 = 1@
  | otherwise =
      case geoWidth w of
        (w2, LeqProof) ->
          -- Coset @{ k0 + j·2^{r-2} }@ at width @w-2@; nonempty meet with
          -- 'log5Odd' iff some stored @k ≡ k0 (mod 2^{r-2})@.
          case S.exactMeet w2 lo (logCoset w2 v k0) of
            Nothing -> False
            Just _  -> True
  where
    m = modulus w
    mMinus1 = m - 1
    xm = x .&. mMinus1
    v = lowBit xm
    r = NR.widthVal w - v
    odd' = xm `shiftR` v
    kClass = if odd' .&. 2 == 0 then OneMod4 else ThreeMod4
    -- Discrete log of the odd part, taken at the reduced modulus @2^r@; this is
    -- exactly the residue of any valid @k@ modulo @2^{r-2}@.
    mr = 1 `shiftL` r
    oddR = odd' .&. (mr - 1)
    u = if kClass == OneMod4 then oddR else (mr - oddR) .&. (mr - 1)
    k0 = dlog5 mr u

-- | The coset @{ k : k ≡ k0 (mod 2^{r-2}) }@ as a width-@(w-2)@ progression,
-- where @r = w - v@. For @v = 0@ this is the singleton @{k0}@ (the log is fully
-- determined); for @v ≥ 1@ it is the full coset with stride @2^{r-2}@.
logCoset :: (1 <= wk) => NatRepr wk -> Int -> Natural -> S.Domain wk
logCoset w2 v k0
  | v == 0    = S.mk w2 k0 1 0
  | otherwise =
      let stride = 1 `shiftL` (NR.widthVal w2 - v)
      in S.mk w2 (k0 .&. (stride - 1)) stride ((1 `shiftL` v) - 1)

-- | Is the concrete odd-class @xoc@ admitted by the abstract class @oc@?
oddClassMember :: OddClass -> OddClass -> Bool
oddClassMember OddClassTop _ = True
oddClassMember oc xoc = oc == xoc

-- | Enumerate the members of the set, ascending, with no duplicates.
--
-- Note: the coordinate representation is /not/ injective into concrete values.
-- When a valuation @v@ is large, @2^v · u (mod 2^w)@ depends only on the low
-- @w-v@ bits of the odd part @u@, so distinct coordinate triples can denote the
-- same value (e.g. @8 · u ≡ 8 (mod 16)@ for every odd @u@). The concretization
-- is therefore a genuine /set/; we deduplicate here.
toList :: (3 <= w) => NatRepr w -> Domain w -> [Natural]
toList w (Domain tz oc lo) =
  Set.toAscList $ Set.fromList
    [ recompose w v c k
    | v <- S.toList tz
    , c <- oddClassElems oc
    , k <- S.toList lo
    ]

-- | The concrete odd classes covered by an abstract class.
oddClassElems :: OddClass -> [OddClass]
oddClassElems OneMod4     = [OneMod4]
oddClassElems ThreeMod4   = [ThreeMod4]
oddClassElems OddClassTop = [OneMod4, ThreeMod4]

-- | The number of distinct values in the represented set.
--
-- Exact and polynomial-time (no enumeration). Values with distinct valuations
-- are themselves distinct (the valuation is @ctz@), so the count is a sum over
-- the @≤ w@ valuations in 'trailingZeroes'. For a valuation @v@ with
-- @r = w - v@: there is @1@ value when @r = 1@ (the odd part is irrelevant
-- modulo @2^1@); @|oddClass|@ values when @r = 2@; and otherwise
-- @|oddClass|@ times the number of /distinct/ residues of 'log5Odd' modulo
-- @2^{r-2}@ (since @2^v · 5^k@ depends only on @k mod 2^{r-2}@).
size :: (3 <= w) => NatRepr w -> Domain w -> Natural
size w (Domain tz oc lo) =
  sum [ perValuation (NR.widthVal w - fromIntegral v) | v <- S.toList tz ]
  where
    ocCount = fromIntegral (length (oddClassElems oc))
    perValuation r
      | r == 1 = 1
      | r == 2 = ocCount
      | otherwise = ocCount * distinctResiduesModPow2 lo (r - 2)

-- | The number of distinct residues of a strides progression modulo @2^t@.
-- Closed form: if the stride is @≡ 0 (mod 2^t)@ every member shares a residue
-- (so @1@); otherwise the residues cycle with period @2^t \/ gcd(stride, 2^t)@,
-- capped by the number of members.
distinctResiduesModPow2 :: S.Domain wk -> Int -> Natural
distinctResiduesModPow2 c t
  | strideModT == 0 = 1
  | otherwise = min (S.n c + 1) orbit
  where
    mt = 1 `shiftL` t
    strideModT = S.stride c .&. (mt - 1)
    g = strideModT .&. (mt - strideModT)   -- gcd(stride, 2^t), both powers-of-two-friendly
    orbit = mt `div` g

-- | Lattice order: is every member of @a@ also a member of @b@? Computed
-- componentwise.
leq :: (3 <= w) => NatRepr w -> Domain w -> Domain w -> Bool
leq _w (Domain tzA ocA loA) (Domain tzB ocB loB) =
  S.leq tzA tzB
  && oddClassLeq ocA ocB
  && S.leq loA loB

-- | The 3-element 'OddClass' lattice order.
oddClassLeq :: OddClass -> OddClass -> Bool
oddClassLeq _ OddClassTop = True
oddClassLeq a b = a == b

-- | Join in the 'OddClass' lattice.
oddClassJoin :: OddClass -> OddClass -> OddClass
oddClassJoin a b
  | a == b = a
  | otherwise = OddClassTop

-- | Meet in the 'OddClass' lattice ('Nothing' = empty, when the two classes
-- are distinct and neither is top).
oddClassMeet :: OddClass -> OddClass -> Maybe OddClass
oddClassMeet OddClassTop b = Just b
oddClassMeet a OddClassTop = Just a
oddClassMeet a b
  | a == b    = Just a
  | otherwise = Nothing

-- ------------------------------------------------------------------
-- * Arithmetic

-- | Multiply two values' odd-class coordinates: the @ℤ\/2@ group operation on
-- the @(-1)^κ@ factor (exclusive-or of the @κ@ bits), lifted over 'OddClassTop'.
oddClassMul :: OddClass -> OddClass -> OddClass
oddClassMul OddClassTop _ = OddClassTop
oddClassMul _ OddClassTop = OddClassTop
oddClassMul OneMod4 b = b           -- κ = 0 is the identity
oddClassMul a OneMod4 = a
oddClassMul ThreeMod4 ThreeMod4 = OneMod4

-- | The kernel singleton @{1}@: valuation 0, class @≡ 1 (mod 4)@, log 0.
one :: (3 <= w) => NatRepr w -> Domain w
one w = case geoWidth w of
  (w2, LeqProof) -> mk w (S.mk w 0 1 0) OneMod4 (S.mk w2 0 1 0)

-- | Negate every value in the set. Total (a nonzero value negates to a nonzero
-- value): @-x = (-1) · x@ multiplies the odd part by @-1 ≡ 3 (mod 4)@, so it
-- flips 'oddClass' and leaves 'trailingZeroes' and 'log5Odd' unchanged.
negate :: (3 <= w) => NatRepr w -> Domain w -> Domain w
negate _w (Domain tz oc lo) = Domain tz (oddClassMul ThreeMod4 oc) lo

-- | Multiply two kernel sets. Because multiplication has zero divisors, the
-- product can include @0@ (when the valuations sum to @≥ w@); this is reported
-- separately for the wrapper to place. Returns the nonzero part of the product
-- (or 'Nothing' when every product is zero) together with a flag indicating
-- whether @0@ is a possible product.
--
-- Coordinates combine independently: @x·y = 2^{v+v'} · (-1)^{κ⊕κ'} ·
-- 5^{k+k'}@. The valuation set is computed exactly (as an integer Minkowski sum,
-- then clamped to @[0,w)@); 'oddClass' combines via 'oddClassMul'; 'log5Odd'
-- combines by 'S.add' at width @w-2@ (sound, and exact when an operand is a
-- singleton — the common \"multiply by a constant\" case).
mul ::
  (3 <= w) =>
  NatRepr w -> Domain w -> Domain w -> (Maybe (Domain w), Bool)
mul w (Domain tzA ocA loA) (Domain tzB ocB loB) =
  case geoWidth w of
    (w2, LeqProof) ->
      let oc = oddClassMul ocA ocB
          lo = S.add w2 loA loB
          vsum = [ va + vb | va <- S.toList tzA, vb <- S.toList tzB ]
      in finishArith w oc lo vsum

-- | Square every value: @x² = 2^{2v} · (-1)^0 · 5^{2k}@ (the @ℤ\/2@ coordinate
-- always becomes @0@, since @κ ⊕ κ = 0@). Like 'mul', squaring can overflow to
-- @0@.
square ::
  (3 <= w) =>
  NatRepr w -> Domain w -> (Maybe (Domain w), Bool)
square w = powN w 2

-- | Raise every value to a fixed nonnegative power @e@: @x^e = 2^{e·v} ·
-- (-1)^{e·κ} · 5^{e·k}@. @e = 0@ yields the singleton @{1}@ (never zero); for
-- @e ≥ 1@ the valuation scales (over integers, so overflow to @0@ is detected
-- exactly), 'oddClass' is unchanged when @e@ is odd and collapses to 'OneMod4'
-- when @e@ is even, and 'log5Odd' scales by @e@ at width @w-2@.
pow ::
  (3 <= w) =>
  NatRepr w -> Integer -> Domain w -> (Maybe (Domain w), Bool)
pow w e c
  | e < 0 = error "GeoStrides.pow: negative exponent"
  | otherwise = powN w (fromInteger e) c

-- | Shared implementation of 'square' \/ 'pow' for a nonnegative integer power.
powN ::
  (3 <= w) =>
  NatRepr w -> Natural -> Domain w -> (Maybe (Domain w), Bool)
powN w e (Domain tz oc lo)
  | e == 0 =
      -- @x^0 = 1@: valuation 0, class @≡ 1 (mod 4)@, log 0.
      case geoWidth w of
        (w2, LeqProof) -> (Just (mk w (S.mk w 0 1 0) OneMod4 (S.mk w2 0 1 0)), False)
  | otherwise =
      case geoWidth w of
        (w2, LeqProof) ->
          let oc' = if Prelude.even e then OneMod4 else oc
              lo' = S.scale w2 (toInteger e) lo
              vscaled = [ e * v | v <- S.toList tz ]
          in finishArith w oc' lo' vscaled

-- | Left shift by a constant @s@: @x << s = x · 2^s@, which adds @s@ to every
-- valuation, leaving 'oddClass' and 'log5Odd' unchanged. Valuations reaching
-- @≥ w@ denote @0@ (reported via the flag), as in 'mul'.
shl ::
  (3 <= w) =>
  NatRepr w -> Domain w -> Natural -> (Maybe (Domain w), Bool)
shl w (Domain tz oc lo) s =
  finishArith w oc lo [ v + s | v <- S.toList tz ]

-- | Assemble an arithmetic result from a combined odd-class, a combined
-- 'log5Odd' axis, and the (integer, unclamped) multiset of resulting valuations.
-- Splits the valuations into the in-range part @[0,w)@ (the nonzero kernel
-- result, with its 'trailingZeroes' the tightest progression covering that set)
-- and a flag for whether any valuation reached @≥ w@ (a zero product).
finishArith ::
  (3 <= w) =>
  NatRepr w -> OddClass -> S.Domain (w - 2) -> [Natural] -> (Maybe (Domain w), Bool)
finishArith w oc lo vsum =
  NR.withLeqProof (oneLeqW w) $
  let wv = NR.natValue w
      inRange = dedupAsc [ v | v <- vsum, v < wv ]
      mayZero = Prelude.any (>= wv) vsum
  in case S.fromAscEltList w inRange of
       Nothing  -> (Nothing, mayZero)      -- every product overflowed to zero
       Just tz' -> (Just (mk w tz' oc lo), mayZero)

-- | Sort and remove duplicates.
dedupAsc :: [Natural] -> [Natural]
dedupAsc = Set.toAscList . Set.fromList

-- | Whether multiplying @a@ by @b@ can produce @0@: some pair of valuations
-- sums to @≥ w@. (Exposed for the wrapper; equivalent to the flag returned by
-- 'mul'.)
mayBeZero :: (3 <= w) => NatRepr w -> Domain w -> Domain w -> Bool
mayBeZero w (Domain tzA _ _) (Domain tzB _ _) =
  let wv = NR.natValue w
  in Prelude.or [ va + vb >= wv | va <- S.toList tzA, vb <- S.toList tzB ]

-- ------------------------------------------------------------------
-- * Lattice operations

-- ------------------------------------------------------------------
-- ** Joins

-- | The join (least upper bound) of two kernel sets: componentwise join on each
-- coordinate axis. Sound (the result contains both operands); since both
-- operands are nonzero, so is the join.
pseudoJoin :: (3 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
pseudoJoin w (Domain tzA ocA loA) (Domain tzB ocB loB) =
  NR.withLeqProof (oneLeqW w) $
  case geoWidth w of
    (w2, LeqProof) ->
      mk w (S.pseudoJoin w tzA tzB)
           (oddClassJoin ocA ocB)
           (S.pseudoJoin w2 loA loB)

-- ------------------------------------------------------------------
-- ** Meets

-- | A /sound over-approximation/ of the meet (intersection) of two kernel sets.
-- Returns 'Nothing' exactly when the intersection is empty.
--
-- A componentwise meet would be /unsound/ here: the coordinate representation is
-- not injective (see 'toList'), so at high valuations the odd-part coordinates
-- collapse — e.g. at @w = 4@, @recompose 3 OneMod4 0 = recompose 3 ThreeMod4 0 =
-- 8@ — and intersecting 'oddClass' would wrongly drop @8@ even though it lies in
-- both operands. Instead we are exact on the /valuation/ axis and widen the
-- odd-part axes: the valuation is @ctz@, so values with distinct valuations are
-- distinct, and conversely whenever the operands share a valuation @v@ they
-- share at least one value of that valuation. Hence:
--
--   * 'trailingZeroes' is the exact intersection of the operands' valuation
--     sets (empty intersection ⇒ 'Nothing');
--   * 'oddClass' and 'log5Odd' are widened to top.
--
-- This is sound and keeps the headline valuation precision (powers-of-two and
-- multiplicative-hashing intersections stay tight on the valuation axis), at the
-- cost of odd-part precision in the meet. A fully exact meet is future work.
pseudoMeet ::
  (3 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
pseudoMeet w (Domain tzA _ _) (Domain tzB _ _) =
  NR.withLeqProof (oneLeqW w) $
  case geoWidth w of
    (w2, LeqProof) ->
      -- 'S.pseudoMeet' over-approximates the valuation intersection (every
      -- shared valuation is kept) and returns 'Nothing' only when the
      -- valuations are disjoint — sound for our purposes. ('S.exactMeet' would
      -- be unsound: it also returns 'Nothing' when the intersection is
      -- nonempty but not a single progression.)
      case S.pseudoMeet w tzA tzB of
        Nothing  -> Nothing
        Just tz' -> Just (mk w tz' OddClassTop (S.top w2))

-- ------------------------------------------------------------------
-- * Generators

-- | Generate a random kernel element at the given width.
genDomain :: (3 <= w) => NatRepr w -> Gen (Domain w)
genDomain w =
  case geoWidth w of
    (w2, LeqProof) -> do
      tz <- genTrailingZeroes w
      oc <- genOddClass
      lo <- S.genDomain w2
      pure (mk w tz oc lo)

-- | Generate a set of valuations: a strides element all of whose members lie in
-- @[0, w)@. We pick a start and stride and take as many steps as keep us in
-- range.
genTrailingZeroes :: (3 <= w) => NatRepr w -> Gen (S.Domain w)
genTrailingZeroes w = do
  let wv = fromIntegral (NR.natValue w) :: Int
  start <- chooseInt (0, wv - 1)
  stride <- chooseInt (1, max 1 (wv - 1))
  -- Largest step count keeping @start + i*stride < w@.
  let maxI = (wv - 1 - start) `div` stride
  i <- chooseInt (0, maxI)
  pure (S.mk w (fromIntegral start) (fromIntegral stride) (fromIntegral i))

-- | Generate a random odd class (including top).
genOddClass :: Gen OddClass
genOddClass = do
  j <- chooseInt (0, 2)
  pure ([OneMod4, ThreeMod4, OddClassTop] !! j)

-- | Generate a random element of the given kernel set.
genElement :: (3 <= w) => NatRepr w -> Domain w -> Gen Natural
genElement w (Domain tz oc lo) = do
  let vs = S.toList tz
      ocs = oddClassElems oc
      ks = S.toList lo
  vi <- chooseInt (0, length vs - 1)
  oi <- chooseInt (0, length ocs - 1)
  ki <- chooseInt (0, length ks - 1)
  pure (recompose w (vs !! vi) (ocs !! oi) (ks !! ki))

-- | Generate a random kernel set paired with an element it contains.
genPair :: (3 <= w) => NatRepr w -> Gen (Domain w, Natural)
genPair w = do
  c <- genDomain w
  x <- genElement w c
  pure (c, x)

-- ------------------------------------------------------------------
-- * Properties

-- ------------------------------------------------------------------
-- ** 2-adic discrete log

-- | @pow5 m (dlog5 m u) ≡ u@ for odd @u ≡ 1 (mod 4)@.
dlog5Pow5RoundTrip :: Int -> Natural -> Property
dlog5Pow5RoundTrip wRaw uRaw =
  wRaw >= 3 ==> property (pow5 m (dlog5 m u) == u)
  where
    w = (wRaw `mod` 14) + 3
    m = 1 `shiftL` w
    u = ((uRaw .&. (m - 1)) Bits..|. 1) .&. complementBit1
    -- force @≡ 1 (mod 4)@ by clearing bit 1
    complementBit1 = (m - 1) `Bits.xor` 2

-- | @dlog5 m (pow5 m k) ≡ k@ for @k ∈ [0, 2^{w-2})@.
pow5Dlog5RoundTrip :: Int -> Natural -> Property
pow5Dlog5RoundTrip wRaw kRaw =
  wRaw >= 3 ==> property (dlog5 m (pow5 m k) == k)
  where
    w = (wRaw `mod` 14) + 3
    m = 1 `shiftL` w
    k = kRaw .&. ((1 `shiftL` (w - 2)) - 1)

-- | @pow5 m (a + b) ≡ pow5 m a * pow5 m b (mod m)@.
pow5Multiplicative :: Int -> Natural -> Natural -> Property
pow5Multiplicative wRaw a b =
  wRaw >= 3 ==> property (pow5 m (a + b) == (pow5 m a * pow5 m b) .&. (m - 1))
  where
    w = (wRaw `mod` 14) + 3
    m = 1 `shiftL` w

-- | @decompose@ followed by @recompose@ is the identity on nonzero values.
-- Stated at a fixed small width so the @3 <= w@ constraint is concrete.
decomposeRecomposeRoundTrip :: Natural -> Property
decomposeRecomposeRoundTrip xRaw =
  property (case decompose w x of
              Nothing -> x == 0
              Just (v, oc, k) -> recompose w v oc k == x)
  where
    w = knownNat @8
    x = xRaw .&. 0xff

-- ------------------------------------------------------------------
-- ** Queries

-- | Every member produced by 'toList' is a 'member'.
memberToList :: (3 <= w) => NatRepr w -> Domain w -> Property
memberToList w c = property (Prelude.all (member w c) (toList w c))

-- | A generated element is a 'member' and appears in 'toList'.
toListMember :: (3 <= w) => NatRepr w -> Domain w -> Natural -> Property
toListMember w c x =
  member w c x ==> property (x `elem` toList w c)

-- | 'toList' has no duplicate values.
toListNoDuplicates :: (3 <= w) => NatRepr w -> Domain w -> Property
toListNoDuplicates w c =
  let xs = toList w c
  in property (length xs == length (List.nub xs))

-- | 'size' equals the length of 'toList'.
sizeViaToList :: (3 <= w) => NatRepr w -> Domain w -> Property
sizeViaToList w c = property (size w c == fromIntegral (length (toList w c)))

-- ------------------------------------------------------------------
-- ** Arithmetic

-- | Soundness of 'negate': if @x@ is a member of @c@, then @-x@ is a member of
-- @negate c@.
correct_neg :: (3 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_neg w c x =
  member w c x ==>
    property (member w (negate w c) (modNeg w x))

-- | Soundness of 'mul': if @x ∈ a@ and @y ∈ b@, then @x·y (mod 2^w)@ is
-- accounted for — it is a member of the nonzero part, or it is @0@ and the
-- zero flag is set.
correct_mul ::
  (3 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mul w a x b y =
  member w a x ==> member w b y ==>
    property (accountsFor w (mul w a b) (modMul w x y))

-- | Soundness of 'square': if @x ∈ c@, then @x² (mod 2^w)@ is accounted for.
correct_square :: (3 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_square w c x =
  member w c x ==>
    property (accountsFor w (square w c) (modMul w x x))

-- | Soundness of 'pow': if @x ∈ c@, then @x^e (mod 2^w)@ is accounted for, for
-- a small nonnegative exponent.
correct_pow ::
  (3 <= w) => NatRepr w -> Int -> Domain w -> Natural -> Property
correct_pow w eRaw c x =
  member w c x ==>
    property (accountsFor w (pow w e c) (modPow w x e))
  where
    e = toInteger (eRaw `mod` 6)   -- keep exponents small

-- | Does an arithmetic result @(nonzeroPart, mayZero)@ account for the concrete
-- value @z@? Either @z@ is nonzero and a member of the nonzero part, or @z@ is
-- @0@ and the zero flag is set.
accountsFor :: (3 <= w) => NatRepr w -> (Maybe (Domain w), Bool) -> Natural -> Bool
accountsFor w (mc, mayZero) z
  | z == 0 = mayZero
  | otherwise = case mc of
      Nothing -> False
      Just c  -> member w c z

-- | @-x (mod 2^w)@.
modNeg :: NatRepr w -> Natural -> Natural
modNeg w x = (m - (x .&. (m - 1))) .&. (m - 1)
  where m = modulus w

-- | @x·y (mod 2^w)@.
modMul :: NatRepr w -> Natural -> Natural -> Natural
modMul w x y = (x * y) .&. (modulus w - 1)

-- | @x^e (mod 2^w)@.
modPow :: NatRepr w -> Natural -> Integer -> Natural
modPow w x e = go 1 (x .&. (m - 1)) e
  where
    m = modulus w
    go acc _ 0 = acc
    go acc b e' =
      let acc' = if Prelude.odd e' then (acc * b) .&. (m - 1) else acc
      in go acc' ((b * b) .&. (m - 1)) (e' `div` 2)

-- ------------------------------------------------------------------
-- ** Lattice

-- | Soundness of 'pseudoJoin': if @x@ is a member of either operand, it is a
-- member of the join.
correct_pseudoJoin ::
  (3 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_pseudoJoin w a x b y =
  property (leftOK && rightOK)
  where
    j = pseudoJoin w a b
    leftOK  = not (member w a x) || member w j x
    rightOK = not (member w b y) || member w j y

-- | Soundness of 'pseudoMeet': if @x@ is a member of /both/ operands, then the
-- meet is nonempty and @x@ is a member of it.
correct_pseudoMeet ::
  (3 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_pseudoMeet w a b x =
  (member w a x && member w b x) ==>
    property (case pseudoMeet w a b of
                Nothing -> False
                Just c  -> member w c x)

-- | 'leq' is reflexive.
leqReflexive :: (3 <= w) => NatRepr w -> Domain w -> Property
leqReflexive w c = property (leq w c c)

-- | 'leq' is transitive.
leqTransitive ::
  (3 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w -> Property
leqTransitive w a b c =
  (leq w a b && leq w b c) ==> property (leq w a c)

-- | 'OddClass' join is associative.
oddClassJoinAssoc :: OddClass -> OddClass -> OddClass -> Property
oddClassJoinAssoc a b c =
  property (oddClassJoin a (oddClassJoin b c)
            == oddClassJoin (oddClassJoin a b) c)

-- | 'OddClass' meet is associative.
oddClassMeetAssoc :: OddClass -> OddClass -> OddClass -> Property
oddClassMeetAssoc a b c =
  property (meetM (Just a) (oddClassMeet b c)
            == meetM (oddClassMeet a b) (Just c))
  where
    -- Meet lifted over the 'Nothing' = empty sentinel.
    meetM :: Maybe OddClass -> Maybe OddClass -> Maybe OddClass
    meetM mx my = do
      x <- mx
      y <- my
      oddClassMeet x y
