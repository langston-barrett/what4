{-|
Module      : What4.Domains.BV.WI
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Wrapped intervals (/WIs/) are an abstract domain for bitvectors. An element
of the WI domain is one of:

* @bottom@ — the empty set;
* @top@ — the full set @[0, 2^w - 1]@; or
* @delim x y@ — the arc on the bitvector \"number circle\" walking clockwise
  from @x@ to @y@. When @x ≤ y@ unsigned this is just @{x, x+1, ..., y}@;
  otherwise it wraps through the south pole, @{0, ..., y} ∪ {x, ..., 2^w - 1}@.
  The invariant is @x ≠ (y + 1) mod 2^w@; that case is canonicalized to @top@.

This domain comes from /Signedness-Agnostic Program Analysis: Precise Integer
Bounds for Low-Level Code/ (Navas, Schachte, Søndergaard, Stuckey, APLAS '12).

== /Geometry/

Like "What4.Domains.BV.Strides", we conceptualize a WI as an arc on a
\"number circle\":

@
smax = 011..1 --vv-- 100..0 = smin
                --
              /    \\
              \\    /
                --
umin = 000..0 --^^-- 111..1 = umax
@

The /north pole/ @np = L01^(w-1), 10^(w-1)M@ separates the two signed
hemispheres; the /south pole/ @sp = L1^w, 0^wM@ separates the two unsigned
hemispheres.

== /Comparison to other domains/

WIs are stride-1 progressions on the number circle. The strides domain of
"What4.Domains.BV.Strides" is a strict generalization (every WI is a stride-1
progression). The arith domain "What4.Domains.BV.Arith" represents the same
geometric shape but always picks a canonical low endpoint, losing the
left/right bias of the WI representation.

The /interesting/ contribution of the WI literature is /signedness-agnostic/
multiplication ('mul'): split each operand at both poles ('cut'), perform
both signed ('smul') and unsigned ('umul') segment-wise products, intersect
them ('usmul'), and pseudo-join the pieces ('pseudoJoinList'). At width @w@
this can be strictly more precise than working over Arith or Bitwise alone.

== /Lattice structure/

Per APLAS '12 §3.1, @(W_w, ⊑)@ is /not/ a lattice. There are pairs of
incomparable WIs with multiple incomparable minimal upper bounds. The
'pseudoJoin' operator picks the smaller-cardinality bound (breaking ties
lexicographically); 'pseudoJoinList' picks a sound upper bound across an
entire collection.

== /Soundness/

A correctness specification of every operation is given in Cryptol in
@doc\/wi.cry@; the Haskell @correct_*@ predicates here mirror that
specification.
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

module What4.Domains.BV.WI
  ( Domain
  , bvdMask
  , proper
    -- * Construction
  , bottom
  , top
  , delim
  , singleton
    -- * Queries
  , member
  , size
  , isBottom
  , isTop
  , subset
    -- * Lattice
  , complement
  , intersect
  , pseudoJoin
  , pseudoJoinList
  , widen
    -- * Splits (poles)
  , northPole
  , southPole
  , nsplit
  , ssplit
  , cut
    -- * Arithmetic
  , negate
  , add
  , sub
  , umul
  , smul
  , usmul
  , mul
  , udiv
  , urem
  , sdiv
  , srem
    -- * Bitwise operations
  , not
  , and
  , or
  , xor
    -- * Concatenation, extension, selection, and truncation
  , zext
  , sext
  , trunc
    -- * Shifts and rotations
  , shl
  , lshr
  , ashr
    -- * Properties
    -- ** Generators
  , genDomain
  , genElement
  , genPair
    -- ** Internal helpers
  , circLeqAtZero
  , circLeqAnchorMin
  , circLeqAnchorMax
  , msbHighBit
  , removeZeroCovers
  , removeZeroNoZero
  , warrenAndSound
  , warrenOrSound
  , udivSeg
  , uremSeg
  , sdivSeg
  , sremSeg
  , bvAndSeg
  , bvOrSeg
  , bvXorSeg
  , correct_udivSeg
  , correct_uremSeg
  , correct_sdivSeg
  , correct_sremSeg
  , correct_bvAndSeg
  , correct_bvOrSeg
  , correct_bvXorSeg
    -- ** Construction
  , singletonMember
    -- ** Queries
  , complementMember
  , subsetCorrect
  , subsetReflexive
  , intersectCorrect
  , pseudoJoinSound
  , pseudoJoinListSound
  , widenSound
    -- ** Splits
  , nsplitCovers
  , nsplitNotStraddleNP
  , ssplitCovers
  , ssplitNotStraddleSP
  , cutCovers
  , cutNotStraddlePoles
    -- ** Arithmetic
  , correct_neg
  , correct_add
  , correct_sub
  , correct_umul
  , correct_smul
  , correct_usmul
  , correct_mul
  , correct_udiv
  , correct_urem
  , correct_sdiv
  , correct_srem
    -- ** Bitwise operations
  , correct_not
  , correct_and
  , correct_or
  , correct_xor
    -- ** Concatenation, extension, selection, and truncation
  , correct_zero_ext
  , correct_sign_ext
  , correct_trunc
    -- ** Shifts and rotations
  , correct_shl
  , correct_lshr
  , correct_ashr
  ) where

import           Control.Exception (assert)
import           Data.Bits ((.&.), (.|.), shiftL, shiftR)
import qualified Data.Bits as Bits
import           GHC.TypeNats (Nat, type (+), type (<=))
import           Prelude hiding (and, concat, negate, not, or, subtract)
import qualified Prelude

import           Data.Parameterized.NatRepr (NatRepr, LeqProof(..), maxUnsigned)
import qualified Data.Parameterized.NatRepr as NR
import           What4.Domains.Verification (Property, property, (==>), Gen, chooseInteger, chooseInt)

-- | A wrapped interval at width @w@. The mask @2^w - 1@ is cached in the
-- 'Top' and 'Delim' constructors (and is implicit for 'Bottom').
data Domain (w :: Nat)
  = Bottom
  | Top !Integer
    -- ^ @Top mask@ for cached @mask = 2^w - 1@.
  | Delim !Integer !Integer !Integer
    -- ^ @Delim mask x y@ for cached @mask = 2^w - 1@, with the invariant
    -- @x ≠ (y + 1) mod 2^w@ (otherwise 'Top' is canonical).
  deriving (Eq, Ord, Show)

-- | The cached @mask = 2^w - 1@. 'Bottom' has no width, so requires the
-- 'NatRepr'.
bvdMask :: NatRepr w -> Domain w -> Integer
bvdMask w = \case
  Bottom         -> maxUnsigned w
  Top mask       -> mask
  Delim mask _ _ -> mask

-- | The data-structure invariants of 'Domain'.
proper :: NatRepr w -> Domain w -> Bool
proper w = \case
  Bottom -> True
  Top mask -> mask == maxUnsigned w
  Delim mask x y ->
    mask == maxUnsigned w
      && 0 <= x && x <= mask
      && 0 <= y && y <= mask
      && x /= ((y + 1) .&. mask)

-- ------------------------------------------------------------------
-- * Construction

-- | The empty WI.
bottom :: Domain w
bottom = Bottom
{-# INLINE bottom #-}

-- | The full WI at width @w@.
top :: NatRepr w -> Domain w
top w = Top (maxUnsigned w)
{-# INLINE top #-}

-- | Smart constructor: canonicalizes the @x = y + 1 mod 2^w@ case to 'Top'.
-- Asserts both endpoints fit in @w@ bits.
delim :: NatRepr w -> Integer -> Integer -> Domain w
delim w x y =
  assert (0 <= x && x <= mask) $
  assert (0 <= y && y <= mask) $
  if x == ((y + 1) .&. mask) then Top mask else Delim mask x y
  where mask = maxUnsigned w
{-# INLINE delim #-}

-- | The WI containing only the value @x@, masked to @w@ bits.
singleton :: NatRepr w -> Integer -> Domain w
singleton w x = delim w (x .&. mask) (x .&. mask)
  where mask = maxUnsigned w
{-# INLINE singleton #-}

-- ------------------------------------------------------------------
-- * Queries

-- | /O(w)/. Membership: does the WI contain the bitvector @e@? The bitvector
-- is masked to @w@ bits.
member :: Domain w -> Integer -> Bool
member d e = case d of
  Bottom         -> False
  Top _          -> True
  Delim mask x y -> circLeq mask x (e .&. mask) y

-- | /O(1)/. The cardinality of the represented set.
size :: Domain w -> Integer
size = \case
  Bottom         -> 0
  Top mask       -> mask + 1
  Delim mask x y -> ((y - x) .&. mask) + 1

-- | /O(1)/. Is this @bottom@?
isBottom :: Domain w -> Bool
isBottom Bottom = True
isBottom _      = False
{-# INLINE isBottom #-}

-- | /O(1)/. Is this @top@?
isTop :: Domain w -> Bool
isTop (Top _) = True
isTop _       = False
{-# INLINE isTop #-}

-- | /O(w)/. Inclusion: @subset s t@ iff @γ(s) ⊆ γ(t)@. APLAS '12 §3.1.
subset :: Domain w -> Domain w -> Bool
subset Bottom _ = True
subset _ (Top _) = True
subset (Top _) _ = False
subset _ Bottom = False
subset s@(Delim mask a b) t@(Delim _ c d)
  | s == t    = True
  | otherwise =
      memberMask mask t a && memberMask mask t b
      && (Prelude.not (memberMask mask s c)
          || Prelude.not (memberMask mask s d))

-- ------------------------------------------------------------------
-- * Lattice

-- | /O(w)/. Complement on @W_w@ — total: @W_w@ is complemented. The
-- 'Bottom' case is partial because 'Bottom' has no cached width; only call
-- 'complement' on a result of an operation that knows its width.
complement :: Domain w -> Domain w
complement = \case
  Bottom         -> error "complement: bottom has no cached width"
  Top _          -> Bottom
  Delim mask x y -> Delim mask ((y + 1) .&. mask) ((x - 1) .&. mask)

-- | /O(w)/. Precise WI intersection: returns 0, 1, or 2 WIs whose union is
-- exactly @γ(s) ∩ γ(t)@. APLAS '12 §3.1, page 10.
intersect :: Domain w -> Domain w -> [Domain w]
intersect Bottom _      = []
intersect _      Bottom = []
intersect (Top _) t     = [t]
intersect s     (Top _) = [s]
intersect s@(Delim mask a b) t@(Delim _ c d)
  | s == t = [s]
  -- Each interval has both bounds in the other (Figure 2(b)): two arcs.
  | aInT && bInT && cInS && dInS =
      [delimRaw mask a d, delimRaw mask c b]
  -- s ⊆ t.
  | aInT && bInT = [s]
  -- t ⊆ s.
  | cInS && dInS = [t]
  -- Single overlapping arc spanning @a@ → @d@ (Figure 2(c)).
  | aInT && dInS = [delimRaw mask a d]
  -- Single overlapping arc spanning @c@ → @b@ (Figure 2(c)).
  | bInT && cInS = [delimRaw mask c b]
  | otherwise = []
  where
    aInT = memberMask mask t a
    bInT = memberMask mask t b
    cInS = memberMask mask s c
    dInS = memberMask mask s d

-- | /O(w)/. The biased pseudo-join: picks the smaller-cardinality enclosing
-- WI, breaking ties by lexicographically smaller left endpoint. Sound (the
-- result contains both inputs) but not associative and not monotone — see
-- APLAS '12 §3.1.
pseudoJoin :: Domain w -> Domain w -> Domain w
pseudoJoin Bottom t = t
pseudoJoin s Bottom = s
pseudoJoin (Top mask) _ = Top mask
pseudoJoin _ (Top mask) = Top mask
pseudoJoin s@(Delim mask a b) t@(Delim _ c d)
  | subset s t = t
  | subset t s = s
  -- Mutual containment of bounds (Figure 2(b)): saturates.
  | aInT && bInT && cInS && dInS = Top mask
  -- Asymmetric overlap (Figure 2(c)).
  | bInT && cInS = delimRaw mask a d
  | dInS && aInT = delimRaw mask c b
  -- Disjoint (Figure 2(d)): two candidates. Pick smaller, ties lex on left.
  | sizeBC < sizeDA = delimRaw mask a d
  | sizeBC > sizeDA = delimRaw mask c b
  | a <= c          = delimRaw mask a d
  | otherwise       = delimRaw mask c b
  where
    aInT = memberMask mask t a
    bInT = memberMask mask t b
    cInS = memberMask mask s c
    dInS = memberMask mask s d
    sizeBC = ((c - b - 1) .&. mask) + 1
    sizeDA = ((a - d - 1) .&. mask) + 1

-- | /O(k·w)/ for a list of length @k@. The generalized pseudo-join: a sound
-- upper bound containing every input. Implemented as a left-fold of
-- 'pseudoJoin'; in general not the minimum-cardinality such bound. The
-- paper's exact algorithm (Figure 3) is more involved; left as future work.
pseudoJoinList :: NatRepr w -> [Domain w] -> Domain w
pseudoJoinList _ []       = Bottom
pseudoJoinList _ (d : ds) = Prelude.foldl pseudoJoin d ds

-- | /O(w)/. Widening operator. @widen s t@ is a sound upper bound of @s@ and
-- @t@ that grows fast enough to guarantee fixed-point iteration terminates.
-- This implementation uses the simplest sound choice: if @t ⊑ s@ no change;
-- otherwise saturate to 'top'. APLAS '12 §4 gives a more nuanced operator
-- that doubles the size of the input rather than saturating; we leave that
-- as future work.
widen :: NatRepr w -> Domain w -> Domain w -> Domain w
widen w s t
  | subset t s = s
  | otherwise  = top w

-- ------------------------------------------------------------------
-- * Splits (poles)

-- | /O(1)/. The smallest WI straddling the north pole at width @w@:
-- @np = L01^(w-1), 10^(w-1)M@. Contains @{2^(w-1) - 1, 2^(w-1)}@.
northPole :: NatRepr w -> Domain w
northPole w = Delim mask (half - 1) half
  where
    mask = maxUnsigned w
    half = (mask + 1) `shiftR` 1
{-# INLINE northPole #-}

-- | /O(1)/. The smallest WI straddling the south pole at width @w@:
-- @sp = L1^w, 0^wM@. Contains @{2^w - 1, 0}@.
southPole :: NatRepr w -> Domain w
southPole w = Delim mask mask 0
  where mask = maxUnsigned w
{-# INLINE southPole #-}

-- | /O(w)/. North-pole split: cut a WI at the north pole so that no
-- resulting segment straddles it. Returns 0–2 WIs. APLAS '12 §3.2.
nsplit :: NatRepr w -> Domain w -> [Domain w]
nsplit _ Bottom = []
nsplit _ (Top mask) = [Delim mask 0 (half - 1), Delim mask half mask]
  where half = (mask + 1) `shiftR` 1
nsplit w s@(Delim mask a b)
  | subset (northPole w) s =
      [Delim mask a (half - 1), Delim mask half b]
  | otherwise = [s]
  where half = (mask + 1) `shiftR` 1

-- | /O(w)/. South-pole split.
ssplit :: NatRepr w -> Domain w -> [Domain w]
ssplit _ Bottom = []
ssplit _ (Top mask) =
  [Delim mask 0 (half - 1), Delim mask half mask]
  where half = (mask + 1) `shiftR` 1
ssplit w s@(Delim mask a b)
  | subset (southPole w) s = [Delim mask a mask, Delim mask 0 b]
  | otherwise              = [s]

-- | /O(w)/. Sphere cut: split at /both/ poles. Returns up to 4 segments
-- straddling neither pole. @cut s = ⋃ {ssplit u | u ∈ nsplit s}@.
cut :: NatRepr w -> Domain w -> [Domain w]
cut w s = concatMap (ssplit w) (nsplit w s)

-- ------------------------------------------------------------------
-- * Arithmetic

-- | /O(w)/. Negation.
negate :: NatRepr w -> Domain w -> Domain w
negate _ Bottom = Bottom
negate _ d@(Top _) = d
negate w (Delim mask a b) =
  let m1 = mask + 1
  in delim w ((m1 - b) .&. mask) ((m1 - a) .&. mask)

-- | /O(w)/. Addition. APLAS '12 §3.2.
add :: NatRepr w -> Domain w -> Domain w -> Domain w
add _ Bottom _ = Bottom
add _ _ Bottom = Bottom
add _ d@(Top _) _ = d
add _ _ d@(Top _) = d
add w (Delim mask a b) (Delim _ c d) =
  let m1 = mask + 1
      sa = ((b - a) .&. mask) + 1
      sb = ((d - c) .&. mask) + 1
  in if sa + sb <= m1
       then delim w ((a + c) .&. mask) ((b + d) .&. mask)
       else top w

-- | /O(w)/. Subtraction (signedness-agnostic).
sub :: NatRepr w -> Domain w -> Domain w -> Domain w
sub _ Bottom _ = Bottom
sub _ _ Bottom = Bottom
sub _ d@(Top _) _ = d
sub _ _ d@(Top _) = d
sub w (Delim mask a b) (Delim _ c d) =
  let m1 = mask + 1
      sa = ((b - a) .&. mask) + 1
      sb = ((d - c) .&. mask) + 1
  in if sa + sb <= m1
       then delim w ((a - d) .&. mask) ((b - c) .&. mask)
       else top w

-- | /O(w)/. Unsigned multiplication of two pole-non-straddling WIs. Caller
-- must ensure both operands came from 'cut'. APLAS '12 §3.2.
umul :: NatRepr w -> Domain w -> Domain w -> Domain w
umul _ Bottom _ = Bottom
umul _ _ Bottom = Bottom
umul _ d@(Top _) _ = d
umul _ _ d@(Top _) = d
umul w (Delim mask a b) (Delim _ c d) =
  let m1 = mask + 1
      lo = a * c
      hi = b * d
  in if hi - lo < m1
       then delim w (lo `mod` m1) (hi `mod` m1)
       else top w

-- | /O(w)/. Signed multiplication of two pole-non-straddling WIs.
--
-- Note: the overflow checks for the mixed-hemisphere cases use /signed/
-- integer multiplication, not the unsigned bit-pattern product written in
-- the paper; the paper's formulas are unsound in those cases when the
-- signed range exceeds @2^w@.
smul :: NatRepr w -> Domain w -> Domain w -> Domain w
smul _ Bottom _ = Bottom
smul _ _ Bottom = Bottom
smul _ d@(Top _) _ = d
smul _ _ d@(Top _) = d
smul w (Delim mask a b) (Delim _ c d) =
  let m1 = mask + 1
      ma = msbI mask a; mb = msbI mask b
      mc = msbI mask c; md = msbI mask d
      sgn x = if msbI mask x then x - m1 else x
      asI = sgn a; bsI = sgn b; csI = sgn c; dsI = sgn d
      arc lo hi
        | hi - lo < m1 = delim w (lo `mod` m1) (hi `mod` m1)
        | otherwise    = top w
  in if ma == mb && mb == mc && mc == md && b * d - a * c < m1
       -- All four endpoints in the same hemisphere: La·c, b·dM. Endpoints
       -- as bit-patterns; the unsigned arithmetic agrees with signed mod 2^w.
       then arc (a * c) (b * d)
     else if ma && mb && Prelude.not mc && Prelude.not md
               && bsI * csI - asI * dsI < m1
       -- s in 1-hemisphere (negative), t in 0-hemisphere (non-negative):
       -- bit-pattern arc @La·d, b·cM@.
       then arc (a * d) (b * c)
     else if Prelude.not ma && Prelude.not mb && mc && md
               && asI * dsI - bsI * csI < m1
       -- s in 0-hemisphere, t in 1-hemisphere: bit-pattern arc @Lb·c, a·dM@.
       then arc (b * c) (a * d)
     else top w

-- | /O(w)/. The combined unsigned/signed product on pole-non-straddling
-- WIs: @s ×_us t = (s ×_u t) ∩ (s ×_s t)@. Returns 0, 1, or 2 WIs.
usmul :: NatRepr w -> Domain w -> Domain w -> [Domain w]
usmul w a b = intersect (umul w a b) (smul w a b)

-- | /O(w)/. Full signedness-agnostic multiplication. Cuts each operand at
-- both poles, computes 'usmul' for every segment pair, and pseudo-joins.
-- APLAS '12 §3.2.
mul :: NatRepr w -> Domain w -> Domain w -> Domain w
mul _ Bottom _ = Bottom
mul _ _ Bottom = Bottom
mul w s t =
  pseudoJoinList w
    [ piece
    | u <- cut w s
    , v <- cut w t
    , piece <- usmul w u v
    ]

-- | /O(w)/. Unsigned division. Excludes 0 from the divisor.
udiv :: NatRepr w -> Domain w -> Domain w -> Domain w
udiv _ Bottom _ = Bottom
udiv _ _ Bottom = Bottom
udiv w s t =
  pseudoJoinList w
    [ udivSeg w u v
    | u <- ssplit w s
    , v0 <- ssplit w t
    , v <- removeZero v0
    ]

-- | /O(w)/. Unsigned remainder.
urem :: NatRepr w -> Domain w -> Domain w -> Domain w
urem _ Bottom _ = Bottom
urem _ _ Bottom = Bottom
urem w s t =
  pseudoJoinList w
    [ uremSeg w u v
    | u <- ssplit w s
    , v0 <- ssplit w t
    , v <- removeZero v0
    ]

-- | /O(w)/. Signed division.
sdiv :: NatRepr w -> Domain w -> Domain w -> Domain w
sdiv _ Bottom _ = Bottom
sdiv _ _ Bottom = Bottom
sdiv w s t =
  pseudoJoinList w
    [ sdivSeg w u v
    | u <- nsplit w s
    , v0 <- nsplit w t
    , v <- removeZero v0
    ]

-- | /O(w)/. Signed remainder.
srem :: NatRepr w -> Domain w -> Domain w -> Domain w
srem _ Bottom _ = Bottom
srem _ _ Bottom = Bottom
srem w s t =
  pseudoJoinList w
    [ sremSeg w u v
    | u <- nsplit w s
    , v0 <- nsplit w t
    , v <- removeZero v0
    ]

-- ------------------------------------------------------------------
-- * Bitwise operations

-- | /O(w)/. Bitwise NOT.
not :: NatRepr w -> Domain w -> Domain w
not _ Bottom = Bottom
not _ d@(Top _) = d
not w (Delim mask a b) =
  delim w ((b `Bits.xor` mask) .&. mask) ((a `Bits.xor` mask) .&. mask)

-- | /O(w)/. Bitwise AND. APLAS '12 §3.2 specifies it via south-pole split +
-- Warren's unsigned interval bitwise primitives.
and :: NatRepr w -> Domain w -> Domain w -> Domain w
and w s t =
  pseudoJoinList w
    [ bvAndSeg w u v
    | u <- ssplit w s
    , v <- ssplit w t
    ]

-- | /O(w)/. Bitwise OR.
or :: NatRepr w -> Domain w -> Domain w -> Domain w
or w s t =
  pseudoJoinList w
    [ bvOrSeg w u v
    | u <- ssplit w s
    , v <- ssplit w t
    ]

-- | /O(w)/. Bitwise XOR.
xor :: NatRepr w -> Domain w -> Domain w -> Domain w
xor w s t =
  pseudoJoinList w
    [ bvXorSeg w u v
    | u <- ssplit w s
    , v <- ssplit w t
    ]

-- ------------------------------------------------------------------
-- * Concatenation, extension, selection, and truncation

-- | /O(w)/. Zero extension to width @u > w@.
zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
zext w s u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof -> case s of
      Bottom -> Bottom
      Top _ -> Delim umask 0 (maxUnsigned w)
      Delim _ _ _ ->
        pseudoJoinList u
          [ Delim umask a b
          | piece <- ssplit w s, (a, b) <- delimEndpoints piece ]
  where
    umask = maxUnsigned u

-- | /O(w)/. Sign extension to width @u > w@.
sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
sext w s u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof -> case s of
      Bottom -> Bottom
      Top _ ->
        Delim umask topNeg umask `pseudoJoin` Delim umask 0 (halfW - 1)
      Delim _ _ _ ->
        pseudoJoinList u
          [ Delim umask (extendBits a) (extendBits b)
          | piece <- nsplit w s, (a, b) <- delimEndpoints piece ]
  where
    umask = maxUnsigned u
    halfW = 1 `shiftL` (NR.widthVal w - 1)
    topNeg = umask - halfW + 1
    maxOldMask = (1 `shiftL` NR.widthVal w) - 1
    extendBits x
      | (x `shiftR` (NR.widthVal w - 1)) == 0 = x
      | otherwise = x .|. (umask `Bits.xor` maxOldMask)

-- | /O(w)/. Truncation to width @n < w@.
trunc ::
  forall n w.
  (1 <= n, n + 1 <= w) =>
  NatRepr n -> NatRepr w -> Domain w -> Domain n
trunc n w = \case
  Bottom -> Bottom
  Top _ -> Top nmask
  Delim _ a b ->
    let aHi = a `shiftR` NR.widthVal n
        bHi = b `shiftR` NR.widthVal n
        aLo = a .&. nmask
        bLo = b .&. nmask
    in if aHi == bHi && aLo <= bLo
         then delim n aLo bLo
       else if (aHi + 1) .&. wmask == bHi && aLo > bLo
         then delim n aLo bLo
       else Top nmask
  where
    nmask = maxUnsigned n
    wmask = maxUnsigned w

-- ------------------------------------------------------------------
-- * Shifts and rotations

-- | /O(w)/. Logical left shift by a constant amount. APLAS '12 §3.2.
shl :: NatRepr w -> Domain w -> Int -> Domain w
shl _ Bottom _ = Bottom
shl _ d k | k <= 0 = d
shl w _ k | k >= NR.widthVal w = singleton w 0
shl _ (Top mask) k = Delim mask 0 ((mask `shiftL` k) .&. mask)
shl w (Delim mask a b) k =
  let lowMask = (1 `shiftL` (NR.widthVal w - k)) - 1
      aHi = a `shiftR` (NR.widthVal w - k)
      bHi = b `shiftR` (NR.widthVal w - k)
      aLo = a .&. lowMask
      bLo = b .&. lowMask
      truncOk = aHi == bHi && aLo <= bLo
             || ((aHi + 1) .&. (mask `shiftR` k)) == bHi && aLo > bLo
  in if truncOk
       then delim w ((a `shiftL` k) .&. mask) ((b `shiftL` k) .&. mask)
       else Delim mask 0 ((mask `shiftL` k) .&. mask)

-- | /O(w)/. Logical right shift by a constant amount.
lshr :: NatRepr w -> Domain w -> Int -> Domain w
lshr _ Bottom _ = Bottom
lshr _ d 0 = d
lshr _ (Top mask) k = Delim mask 0 (mask `shiftR` k)
lshr w s@(Delim mask a b) k
  | subset (southPole w) s = Delim mask 0 (mask `shiftR` k)
  | otherwise              = delim w (a `shiftR` k) (b `shiftR` k)

-- | /O(w)/. Arithmetic right shift by a constant amount.
ashr :: NatRepr w -> Domain w -> Int -> Domain w
ashr _ Bottom _ = Bottom
ashr _ d 0 = d
ashr _ (Top mask) k =
  let half = (mask + 1) `shiftR` 1
      lo   = ((mask `Bits.xor` (half - 1)) `shiftR` k) .&. mask
      hi   = (half - 1) `shiftR` k
  in pseudoJoin (Delim mask lo mask) (Delim mask 0 hi)
ashr w s@(Delim mask a b) k
  | subset (northPole w) s =
      let half = (mask + 1) `shiftR` 1
          lo   = ((mask `Bits.xor` (half - 1)) `shiftR` k) .&. mask
          hi   = (half - 1) `shiftR` k
      in pseudoJoin (Delim mask lo mask) (Delim mask 0 hi)
  | otherwise =
      let arShift x =
            if msbI mask x
              then ((x `shiftR` k)
                    .|. (mask `Bits.xor` (mask `shiftR` k))) .&. mask
              else (x `shiftR` k) .&. mask
      in delim w (arShift a) (arShift b)

-- ------------------------------------------------------------------
-- * Internal helpers

-- | @circLeq m x a b@: starting from @x@ on the bitvector circle of size
-- @mask + 1 = 2^w@, is @a@ encountered no later than @b@ when walking
-- clockwise?
circLeq :: Integer -> Integer -> Integer -> Integer -> Bool
circLeq m x a b = (a + nx) .&. m <= (b + nx) .&. m
  where nx = (m + 1 - x) .&. m

-- | Membership test threading the cached mask.
memberMask :: Integer -> Domain w -> Integer -> Bool
memberMask _ Bottom _ = False
memberMask _ (Top _) _ = True
memberMask m (Delim _ x y) e = circLeq m x (e .&. m) y

-- | Most-significant bit at width with mask @m@: 'True' iff @x ≥ 2^(w-1)@.
msbI :: Integer -> Integer -> Bool
msbI m x = (x .&. ((m + 1) `shiftR` 1)) /= 0

-- | Drop the value @0@ from a WI, returning at most two non-empty WIs.
removeZero :: Domain w -> [Domain w]
removeZero Bottom = []
removeZero (Top mask) = intersect (Top mask) (Delim mask 1 mask)
removeZero d@(Delim mask _ _) = intersect d (Delim mask 1 mask)

-- | Endpoint pair for a 'Delim' value, as a list (empty for non-delim).
delimEndpoints :: Domain w -> [(Integer, Integer)]
delimEndpoints (Delim _ a b) = [(a, b)]
delimEndpoints _             = []

-- | @delimRaw mask x y@: build a 'Delim' or canonicalize to 'Top' when the
-- invariant @x ≠ y + 1@ would be violated.
delimRaw :: Integer -> Integer -> Integer -> Domain w
delimRaw mask x y
  | x == ((y + 1) .&. mask) = Top mask
  | otherwise               = Delim mask x y

-- | Unsigned division on a south-pole-split (and divisor-non-zero) pair.
udivSeg :: NatRepr w -> Domain w -> Domain w -> Domain w
udivSeg _ Bottom _ = Bottom
udivSeg _ _ Bottom = Bottom
udivSeg _ d@(Top _) _ = d
udivSeg w (Delim _ a b) (Delim _ c d)
  | c == 0 || d == 0 = Bottom
  | otherwise        = delim w (a `Prelude.div` d) (b `Prelude.div` c)
udivSeg _ (Delim _ _ _) (Top _) = Bottom

-- | Unsigned remainder on a south-pole-split (and divisor-non-zero) pair.
uremSeg :: NatRepr w -> Domain w -> Domain w -> Domain w
uremSeg _ Bottom _ = Bottom
uremSeg _ _ Bottom = Bottom
uremSeg w (Top _) (Delim _ _ d) = delim w 0 (d - 1)
uremSeg w (Delim _ _ b) (Delim _ _ d) =
  delim w 0 (Prelude.min b (d - 1))
uremSeg _ _ (Top _) = Bottom

-- | Signed division on a north-pole-split (and divisor-non-zero) pair.
sdivSeg :: NatRepr w -> Domain w -> Domain w -> Domain w
sdivSeg _ Bottom _ = Bottom
sdivSeg _ _ Bottom = Bottom
sdivSeg _ d@(Top _) _ = d
sdivSeg _ _ d@(Top _) = d
sdivSeg w (Delim mask a b) (Delim _ c d) =
  let m1 = mask + 1
      sgn x = if msbI mask x then x - m1 else x
      asI = sgn a; bsI = sgn b
      csI = sgn c; dsI = sgn d
      candidates =
        [ asI `Prelude.quot` csI, asI `Prelude.quot` dsI
        , bsI `Prelude.quot` csI, bsI `Prelude.quot` dsI ]
      lo = Prelude.minimum candidates
      hi = Prelude.maximum candidates
      asMod x = x .&. mask
  in if hi - lo + 1 > m1
       then top w
       else delim w (asMod lo) (asMod hi)

-- | Signed remainder on a north-pole-split pair. Splits the dividend at zero
-- and bounds each side separately.
sremSeg :: NatRepr w -> Domain w -> Domain w -> Domain w
sremSeg _ Bottom _ = Bottom
sremSeg _ _ Bottom = Bottom
sremSeg _ d@(Top _) _ = d
sremSeg _ _ d@(Top _) = d
sremSeg w (Delim mask a b) (Delim _ c d) =
  let m1 = mask + 1
      sgn x = if msbI mask x then x - m1 else x
      asI = sgn a; bsI = sgn b
      bound = Prelude.max (Prelude.abs (sgn c)) (Prelude.abs (sgn d)) - 1
      negPart
        | asI < 0   = delim w ((Prelude.negate bound) .&. mask) 0
        | otherwise = Bottom
      posPart
        | bsI >= 0  = delim w 0 (Prelude.min bsI bound)
        | otherwise = Bottom
  in pseudoJoin negPart posPart

-- | Bitwise AND on an ssplit-segment pair.
bvAndSeg :: NatRepr w -> Domain w -> Domain w -> Domain w
bvAndSeg _ Bottom _ = Bottom
bvAndSeg _ _ Bottom = Bottom
bvAndSeg w (Top _) (Delim _ _ bhi) = delim w 0 bhi
bvAndSeg w (Delim _ _ ahi) (Top _) = delim w 0 ahi
bvAndSeg _ d@(Top _) (Top _) = d
bvAndSeg w (Delim mask alo ahi) (Delim _ blo bhi) =
  delim w (warrenAndLo mask alo ahi blo bhi) (warrenAndHi mask alo ahi blo bhi)

-- | Bitwise OR on an ssplit-segment pair.
bvOrSeg :: NatRepr w -> Domain w -> Domain w -> Domain w
bvOrSeg _ Bottom _ = Bottom
bvOrSeg _ _ Bottom = Bottom
bvOrSeg w (Top mask) (Delim _ blo _) = delim w blo mask
bvOrSeg w (Delim _ alo _) (Top mask) = delim w alo mask
bvOrSeg _ d@(Top _) (Top _) = d
bvOrSeg w (Delim mask alo ahi) (Delim _ blo bhi) =
  delim w (warrenOrLo mask alo ahi blo bhi) (warrenOrHi mask alo ahi blo bhi)

-- | Bitwise XOR on an ssplit-segment pair. Conservative envelope @[0,
-- fillright (ahi | bhi)]@; a tighter Warren-style bound is left as future
-- work.
bvXorSeg :: NatRepr w -> Domain w -> Domain w -> Domain w
bvXorSeg _ Bottom _ = Bottom
bvXorSeg _ _ Bottom = Bottom
bvXorSeg _ d@(Top _) _ = d
bvXorSeg _ _ d@(Top _) = d
bvXorSeg w (Delim _ _ ahi) (Delim _ _ bhi) =
  delim w 0 (fillright (ahi .|. bhi))
  where
    fillright x = go 1
      where
        go !k | k > x     = k - 1
              | otherwise = go (k * 2)

-- ------------------------------------------------------------------
-- * Warren's unsigned bitwise primitives
--
-- /Hacker's Delight/ §4.3 (and-bound) and §4.4 (or-bound). Given two
-- unsigned ranges @[alo, ahi]@ and @[blo, bhi]@, return tight bounds for
-- the bitwise AND or OR of any two members. O(w).

warrenAndLo :: Integer -> Integer -> Integer -> Integer -> Integer -> Integer
warrenAndLo mask alo ahi blo bhi = go alo blo (1 `shiftL` (bitWidth - 1))
  where
    bitWidth = Bits.popCount mask
    go a b 0 = a .&. b
    go a b m
      | (Bits.complement a .&. Bits.complement b .&. m) /= 0
      , let aPrime = (a .|. m) .&. complementBelow m
      , aPrime <= ahi
      = aPrime .&. b
      | (Bits.complement a .&. Bits.complement b .&. m) /= 0
      , let bPrime = (b .|. m) .&. complementBelow m
      , bPrime <= bhi
      = a .&. bPrime
      | otherwise = go a b (m `shiftR` 1)
    complementBelow m = Bits.complement (m - 1)

warrenAndHi :: Integer -> Integer -> Integer -> Integer -> Integer -> Integer
warrenAndHi mask alo _ blo bhi = go bhi bhi (1 `shiftL` (bitWidth - 1))
  where
    bitWidth = Bits.popCount mask
    go a b 0 = a .&. b
    go a b m
      | (a .&. Bits.complement b .&. m) /= 0
      , let aPrime = (a .&. Bits.complement m) .|. (m - 1)
      , aPrime >= alo
      = aPrime .&. b
      | (Bits.complement a .&. b .&. m) /= 0
      , let bPrime = (b .&. Bits.complement m) .|. (m - 1)
      , bPrime >= blo
      = a .&. bPrime
      | otherwise = go a b (m `shiftR` 1)

warrenOrLo :: Integer -> Integer -> Integer -> Integer -> Integer -> Integer
warrenOrLo mask alo ahi blo bhi = go alo blo (1 `shiftL` (bitWidth - 1))
  where
    bitWidth = Bits.popCount mask
    go a b 0 = a .|. b
    go a b m
      | (Bits.complement a .&. b .&. m) /= 0
      , let aPrime = (a .|. m) .&. complementBelow m
      , aPrime <= ahi
      = aPrime .|. b
      | (a .&. Bits.complement b .&. m) /= 0
      , let bPrime = (b .|. m) .&. complementBelow m
      , bPrime <= bhi
      = a .|. bPrime
      | otherwise = go a b (m `shiftR` 1)
    complementBelow m = Bits.complement (m - 1)

warrenOrHi :: Integer -> Integer -> Integer -> Integer -> Integer -> Integer
warrenOrHi mask alo ahi blo bhi = go ahi bhi (1 `shiftL` (bitWidth - 1))
  where
    bitWidth = Bits.popCount mask
    go a b 0 = a .|. b
    go a b m
      | (a .&. b .&. m) /= 0
      , let aPrime = (a - m) .|. (m - 1)
      , aPrime >= alo
      = aPrime .|. b
      | (a .&. b .&. m) /= 0
      , let bPrime = (b - m) .|. (m - 1)
      , bPrime >= blo
      = a .|. bPrime
      | otherwise = go a b (m `shiftR` 1)

-- ------------------------------------------------------------------
-- * Generators

-- | Generator for a (proper) 'Domain' at width @w@.
genDomain :: NatRepr w -> Gen (Domain w)
genDomain w = do
  let mask = maxUnsigned w
  shape <- chooseInt (0, 9)
  if shape == 0 then pure Bottom
  else if shape == 1 then pure (Top mask)
  else do
    x <- chooseInteger (0, mask)
    y <- chooseInteger (0, mask)
    pure (delim w x y)

-- | Generate an element of a non-bottom 'Domain'.
genElement :: Domain w -> Gen Integer
genElement = \case
  Bottom -> error "genElement: bottom"
  Top mask -> chooseInteger (0, mask)
  Delim mask x y ->
    if x <= y
      then chooseInteger (x, y)
      else do
        b <- chooseInt (0, 1)
        if b == 0 then chooseInteger (0, y)
                  else chooseInteger (x, mask)

-- | Generate a non-bottom domain and an element of it.
genPair :: NatRepr w -> Gen (Domain w, Integer)
genPair w = do
  d <- nonBottomDomain
  x <- genElement d
  pure (d, x)
  where
    nonBottomDomain = do
      d <- genDomain w
      case d of
        Bottom -> nonBottomDomain
        _      -> pure d

-- ------------------------------------------------------------------
-- * Correctness properties

-- ------------------------------------------------------------------
-- ** Internal helpers

-- | @circLeq m 0@ degenerates to ordinary unsigned @<=@.
circLeqAtZero :: Integer -> Integer -> Int -> Property
circLeqAtZero a b k =
  k >= 1 ==> property (circLeq m 0 a' b' == (a' <= b'))
  where
    m  = (1 `shiftL` k) - 1
    a' = a .&. m
    b' = b .&. m

-- | The anchor @x@ is the minimum: @circLeq m x x v@ always holds.
circLeqAnchorMin :: Integer -> Integer -> Int -> Property
circLeqAnchorMin x v k =
  k >= 1 ==> property (circLeq m (x .&. m) (x .&. m) (v .&. m))
  where m = (1 `shiftL` k) - 1

-- | The predecessor of @x@ is the maximum: @circLeq m x v (x - 1)@ always
-- holds.
circLeqAnchorMax :: Integer -> Integer -> Int -> Property
circLeqAnchorMax x v k =
  k >= 1 ==>
    property (circLeq m x' (v .&. m) ((x' + m) .&. m))
  where
    m  = (1 `shiftL` k) - 1
    x' = x .&. m

-- | @msbI@ agrees with the high-bit interpretation: @msbI m x@ iff the
-- masked bit-pattern is @≥ 2^(w-1)@.
msbHighBit :: Integer -> Int -> Property
msbHighBit x k =
  k >= 1 ==> property (msbI m x' == (x' >= (m + 1) `shiftR` 1))
  where
    m  = (1 `shiftL` k) - 1
    x' = x .&. m

-- | Every non-zero member of @s@ lies in some piece of @removeZero s@.
removeZeroCovers ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Property
removeZeroCovers w s x =
  proper w s ==> member s x' ==> x' /= 0 ==>
    property (Prelude.any (\d -> member d x') (removeZero s))
  where
    x' = x .&. maxUnsigned w

-- | No piece of @removeZero s@ contains @0@.
removeZeroNoZero :: (1 <= w) => NatRepr w -> Domain w -> Property
removeZeroNoZero w s =
  proper w s ==>
    property (Prelude.all (\d -> Prelude.not (member d 0)) (removeZero s))

-- | Soundness of Warren's AND bounds: for any @a ∈ [alo, ahi]@ and
-- @b ∈ [blo, bhi]@, @warrenAndLo ≤ a .&. b ≤ warrenAndHi@. APLAS '12 cites
-- /Hacker's Delight/ §4.3.
warrenAndSound :: Integer -> Integer -> Integer -> Integer -> Int -> Property
warrenAndSound a0 b0 lo0 sz0 k =
  k >= 1 ==> alo <= ahi ==> blo <= bhi ==>
    property (warrenAndLo m alo ahi blo bhi <= ab
           && ab <= warrenAndHi m alo ahi blo bhi)
  where
    m   = (1 `shiftL` k) - 1
    a   = a0 .&. m
    b   = b0 .&. m
    -- Build a range @[lo, lo + sz]@ around @a@ within @[0, m]@.
    alo = Prelude.max 0 (a - (lo0 .&. m))
    ahi = Prelude.min m (a + (sz0 .&. m))
    blo = Prelude.max 0 (b - (lo0 .&. m))
    bhi = Prelude.min m (b + (sz0 .&. m))
    ab  = a .&. b

-- | Soundness of Warren's OR bounds.
warrenOrSound :: Integer -> Integer -> Integer -> Integer -> Int -> Property
warrenOrSound a0 b0 lo0 sz0 k =
  k >= 1 ==> alo <= ahi ==> blo <= bhi ==>
    property (warrenOrLo m alo ahi blo bhi <= ab
           && ab <= warrenOrHi m alo ahi blo bhi)
  where
    m   = (1 `shiftL` k) - 1
    a   = a0 .&. m
    b   = b0 .&. m
    alo = Prelude.max 0 (a - (lo0 .&. m))
    ahi = Prelude.min m (a + (sz0 .&. m))
    blo = Prelude.max 0 (b - (lo0 .&. m))
    bhi = Prelude.min m (b + (sz0 .&. m))
    ab  = a .|. b

-- | 'udivSeg' is sound on south-pole-non-straddling, divisor-non-zero
-- pairs.
correct_udivSeg ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_udivSeg w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==> y /= 0 ==>
    Prelude.not (subset (southPole w) a) ==>
    Prelude.not (subset (southPole w) b) ==>
    Prelude.not (member b 0) ==>
      property (member (udivSeg w a b) (x `Prelude.quot` y))

-- | 'uremSeg' is sound on south-pole-non-straddling, divisor-non-zero
-- pairs.
correct_uremSeg ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_uremSeg w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==> y /= 0 ==>
    Prelude.not (subset (southPole w) a) ==>
    Prelude.not (subset (southPole w) b) ==>
    Prelude.not (member b 0) ==>
      property (member (uremSeg w a b) (x `Prelude.rem` y))

-- | 'sdivSeg' is sound on north-pole-non-straddling, divisor-non-zero
-- pairs.
correct_sdivSeg ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_sdivSeg w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==> ys /= 0 ==>
    Prelude.not (subset (northPole w) a) ==>
    Prelude.not (subset (northPole w) b) ==>
    Prelude.not (member b 0) ==>
      property (member (sdivSeg w a b)
                       ((xs `Prelude.quot` ys) .&. maxUnsigned w))
  where
    mask = maxUnsigned w
    sgn v = if msbI mask v then v - (mask + 1) else v
    xs = sgn x
    ys = sgn y

-- | 'sremSeg' is sound on north-pole-non-straddling, divisor-non-zero
-- pairs.
correct_sremSeg ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_sremSeg w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==> ys /= 0 ==>
    Prelude.not (subset (northPole w) a) ==>
    Prelude.not (subset (northPole w) b) ==>
    Prelude.not (member b 0) ==>
      property (member (sremSeg w a b)
                       ((xs `Prelude.rem` ys) .&. maxUnsigned w))
  where
    mask = maxUnsigned w
    sgn v = if msbI mask v then v - (mask + 1) else v
    xs = sgn x
    ys = sgn y

-- | 'bvAndSeg' is sound on south-pole-non-straddling pairs.
correct_bvAndSeg ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_bvAndSeg w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    Prelude.not (subset (southPole w) a) ==>
    Prelude.not (subset (southPole w) b) ==>
      property (member (bvAndSeg w a b) (x .&. y))

-- | 'bvOrSeg' is sound on south-pole-non-straddling pairs.
correct_bvOrSeg ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_bvOrSeg w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    Prelude.not (subset (southPole w) a) ==>
    Prelude.not (subset (southPole w) b) ==>
      property (member (bvOrSeg w a b) (x .|. y))

-- | 'bvXorSeg' is sound on south-pole-non-straddling pairs.
correct_bvXorSeg ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_bvXorSeg w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    Prelude.not (subset (southPole w) a) ==>
    Prelude.not (subset (southPole w) b) ==>
      property (member (bvXorSeg w a b) (x `Bits.xor` y))

-- ------------------------------------------------------------------
-- ** Construction

-- | A 'singleton' WI contains exactly its argument.
singletonMember :: NatRepr w -> Integer -> Property
singletonMember w x =
  property (member (singleton w x) (x .&. maxUnsigned w))

-- ------------------------------------------------------------------
-- ** Queries

-- | @complement@ partitions the universe: every bitvector lies in exactly
-- one of @s@ or @complement s@.
complementMember :: (1 <= w) => NatRepr w -> Domain w -> Integer -> Property
complementMember w c x =
  proper w c ==> Prelude.not (isBottom c) ==> Prelude.not (isTop c) ==>
    property (member c x' /= member (complement c) x')
  where
    x' = x .&. maxUnsigned w

-- | Soundness of 'subset': @subset a b@ implies every element of @a@ is in
-- @b@.
subsetCorrect ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Integer -> Property
subsetCorrect w a b x =
  proper w a ==> proper w b ==>
    subset a b ==> member a x' ==> property (member b x')
  where
    x' = x .&. maxUnsigned w

-- | 'subset' is reflexive.
subsetReflexive :: (1 <= w) => NatRepr w -> Domain w -> Property
subsetReflexive w a = proper w a ==> property (subset a a)

-- | Soundness of 'intersect': any element in some output piece is in both
-- inputs.
intersectCorrect ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Integer -> Property
intersectCorrect w a b x =
  proper w a ==> proper w b ==>
    Prelude.any (\d -> member d x') (intersect a b) ==>
      property (member a x' && member b x')
  where
    x' = x .&. maxUnsigned w

-- | Soundness of 'pseudoJoin': the result contains both inputs.
pseudoJoinSound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Integer -> Property
pseudoJoinSound w a b x =
  proper w a ==> proper w b ==>
    (member a x' || member b x') ==>
      property (member (pseudoJoin a b) x')
  where
    x' = x .&. maxUnsigned w

-- | Soundness of 'pseudoJoinList': the result contains every input.
pseudoJoinListSound ::
  (1 <= w) =>
  NatRepr w -> [Domain w] -> Integer -> Property
pseudoJoinListSound w as x =
  Prelude.all (proper w) as ==>
    Prelude.any (\d -> member d x') as ==>
      property (member (pseudoJoinList w as) x')
  where
    x' = x .&. maxUnsigned w

-- | Soundness of 'widen': the result contains both inputs.
widenSound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Integer -> Property
widenSound w a b x =
  proper w a ==> proper w b ==>
    (member a x' || member b x') ==>
      property (member (widen w a b) x')
  where
    x' = x .&. maxUnsigned w

-- ------------------------------------------------------------------
-- ** Splits

-- | Every element of @s@ lies in some piece of @nsplit s@.
nsplitCovers ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Property
nsplitCovers w s x =
  proper w s ==> member s x' ==>
    property (Prelude.any (\d -> member d x') (nsplit w s))
  where
    x' = x .&. maxUnsigned w

-- | No piece of @nsplit s@ properly contains the north pole.
nsplitNotStraddleNP :: (1 <= w) => NatRepr w -> Domain w -> Property
nsplitNotStraddleNP w s =
  proper w s ==>
    property (Prelude.all (\d -> d == northPole w
                              || Prelude.not (subset (northPole w) d))
                          (nsplit w s))

-- | Every element of @s@ lies in some piece of @ssplit s@.
ssplitCovers ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Property
ssplitCovers w s x =
  proper w s ==> member s x' ==>
    property (Prelude.any (\d -> member d x') (ssplit w s))
  where
    x' = x .&. maxUnsigned w

-- | No piece of @ssplit s@ properly contains the south pole.
ssplitNotStraddleSP :: (1 <= w) => NatRepr w -> Domain w -> Property
ssplitNotStraddleSP w s =
  proper w s ==>
    property (Prelude.all (\d -> d == southPole w
                              || Prelude.not (subset (southPole w) d))
                          (ssplit w s))

-- | Every element of @s@ lies in some piece of @cut s@.
cutCovers ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Property
cutCovers w s x =
  proper w s ==> member s x' ==>
    property (Prelude.any (\d -> member d x') (cut w s))
  where
    x' = x .&. maxUnsigned w

-- | No piece of @cut s@ properly contains either pole.
cutNotStraddlePoles :: (1 <= w) => NatRepr w -> Domain w -> Property
cutNotStraddlePoles w s =
  proper w s ==>
    property (Prelude.all (\d -> d == northPole w
                              || Prelude.not (subset (northPole w) d))
                          (cut w s)
           && Prelude.all (\d -> d == southPole w
                              || Prelude.not (subset (southPole w) d))
                          (cut w s))

-- ------------------------------------------------------------------
-- ** Arithmetic

correct_neg :: (1 <= w) => NatRepr w -> Domain w -> Integer -> Property
correct_neg w c x =
  proper w c ==> member c x ==>
    property (member (negate w c) ((Prelude.negate x) .&. maxUnsigned w))

correct_add ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_add w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    property (member (add w a b) ((x + y) .&. maxUnsigned w))

correct_sub ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_sub w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    property (member (sub w a b) ((x - y) .&. maxUnsigned w))

-- | 'umul' is sound on pole-non-straddling inputs.
correct_umul ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_umul w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    Prelude.not (subset (northPole w) a) ==>
    Prelude.not (subset (southPole w) a) ==>
    Prelude.not (subset (northPole w) b) ==>
    Prelude.not (subset (southPole w) b) ==>
      property (member (umul w a b) ((x * y) .&. maxUnsigned w))

-- | 'smul' is sound on pole-non-straddling inputs.
correct_smul ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_smul w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    Prelude.not (subset (northPole w) a) ==>
    Prelude.not (subset (southPole w) a) ==>
    Prelude.not (subset (northPole w) b) ==>
    Prelude.not (subset (southPole w) b) ==>
      property (member (smul w a b) ((x * y) .&. maxUnsigned w))

-- | 'usmul' is sound on pole-non-straddling inputs: the product lies in some
-- output piece.
correct_usmul ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_usmul w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    Prelude.not (subset (northPole w) a) ==>
    Prelude.not (subset (southPole w) a) ==>
    Prelude.not (subset (northPole w) b) ==>
    Prelude.not (subset (southPole w) b) ==>
      property (Prelude.any (\d -> member d ((x * y) .&. maxUnsigned w))
                            (usmul w a b))

correct_mul ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_mul w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    property (member (mul w a b) ((x * y) .&. maxUnsigned w))

correct_udiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_udiv w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (udiv w a b) (x `Prelude.quot` y))

correct_urem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_urem w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (urem w a b) (x `Prelude.rem` y))

correct_sdiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_sdiv w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==> ys /= 0 ==>
    property (member (sdiv w a b) ((xs `Prelude.quot` ys) .&. maxUnsigned w))
  where
    mask = maxUnsigned w
    sgn v = if msbI mask v then v - (mask + 1) else v
    xs = sgn x
    ys = sgn y

correct_srem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_srem w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==> ys /= 0 ==>
    property (member (srem w a b) ((xs `Prelude.rem` ys) .&. maxUnsigned w))
  where
    mask = maxUnsigned w
    sgn v = if msbI mask v then v - (mask + 1) else v
    xs = sgn x
    ys = sgn y

-- ------------------------------------------------------------------
-- ** Bitwise operations

correct_not :: (1 <= w) => NatRepr w -> Domain w -> Integer -> Property
correct_not w c x =
  proper w c ==> member c x ==>
    property (member (not w c) ((Bits.complement x) .&. maxUnsigned w))

correct_and ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_and w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    property (member (and w a b) (x .&. y))

correct_or ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_or w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    property (member (or w a b) (x .|. y))

correct_xor ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Domain w -> Integer -> Property
correct_xor w a x b y =
  proper w a ==> proper w b ==> member a x ==> member b y ==>
    property (member (xor w a b) (x `Bits.xor` y))

-- ------------------------------------------------------------------
-- ** Concatenation, extension, selection, and truncation

correct_zero_ext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
correct_zero_ext w c u x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      proper w c ==> member c x ==>
        property (member (zext w c u) (x .&. maxUnsigned w))

correct_sign_ext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Integer -> Property
correct_sign_ext w c u x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      proper w c ==> member c x ==>
        property (member (sext w c u) (xs .&. maxUnsigned u))
  where
    mask = maxUnsigned w
    sgn v = if msbI mask v then v - (mask + 1) else v
    xs = sgn x

correct_trunc ::
  forall n w.
  (1 <= n, n + 1 <= w) =>
  NatRepr n -> NatRepr w -> Domain w -> Integer -> Property
correct_trunc n w a x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 n) (NR.knownNat @1))
                   (LeqProof :: LeqProof (n + 1) w) of
    LeqProof ->
      proper w a ==> member a x ==>
        property (member (trunc n w a) (x .&. maxUnsigned n))

-- ------------------------------------------------------------------
-- ** Shifts and rotations

correct_shl ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Int -> Property
correct_shl w a x k =
  proper w a ==> member a x ==> k >= 0 ==> k <= NR.widthVal w ==>
    property (member (shl w a k) ((x `shiftL` k) .&. maxUnsigned w))

correct_lshr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Int -> Property
correct_lshr w a x k =
  proper w a ==> member a x ==> k >= 0 ==> k <= NR.widthVal w ==>
    property (member (lshr w a k) (x `shiftR` k))

correct_ashr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Int -> Property
correct_ashr w a x k =
  proper w a ==> member a x ==> k >= 0 ==> k <= NR.widthVal w ==>
    property (member (ashr w a k) ((xs `shiftR` k) .&. maxUnsigned w))
  where
    mask = maxUnsigned w
    sgn v = if msbI mask v then v - (mask + 1) else v
    xs = sgn x
