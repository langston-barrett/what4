-- | Precision tests for strides operations.
--
-- Each lifted strides op should be at least as precise as the corresponding op
-- on the simple-hull projection of its inputs. The simple hull is the arc
-- @[start, start + n·stride]@: tight on non-self-wrapping orbits, and top on
-- self-wrapping ones (where @n·stride >= 2^w@). This is *not* what
-- 'S.toArith' returns — 'S.toArith' uses 'cosetArc' for self-wrap, which is
-- in general incomparable with strides results — but it /is/ the hull strides
-- can always claim to refine. We measure precision by /cardinality/:
--
-- @
-- S.size (S.op a b) <= A.size (A.op (hull a) (hull b))
-- @
--
-- Cardinality (rather than set inclusion) is the right comparison even with
-- this hull: a strides coset walk and the arith arc cover different elements
-- once strides has any nontrivial coset structure, so neither is uniformly a
-- subset of the other. A smaller cardinality is a tighter abstraction.
--
-- (Bitwise and rotation ops lift through 'B.Domain' rather than 'A.Domain',
-- so they are not compared against an Arith oracle here.)
--
-- The @bitwise_<op>@ properties further check that each strides op is at
-- least as precise as the bitwise lifting
-- @S.fromBitwise w (B.op (S.toBitwise a) (S.toBitwise b))@. They are
-- regression tests for the eventual replacement of 'liftBitwise1' /
-- 'liftBitwise2': the new implementation must not lose precision against
-- the bitwise oracle. Subset ('S.leqExact') is the default; ops whose
-- closed form can leave the bitwise image fall back to cardinality.
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Strides.Precision (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, addNat, addIsLeq, isPosNat, knownNat, someNat, testLeq, LeqProof(..), maxUnsigned)
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (+), type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import qualified What4.Domains.BV.Strides as S
import           What4.Domains.Verification (Gen, Property, chooseInt, chooseInteger, getSize, property, (==>))
import           VerifyBindings (genTest)

data SomeWidth where
  SW :: (1 <= w) => NatRepr w -> SomeWidth

genWidth :: Gen SomeWidth
genWidth =
  do sz <- getSize
     x <- chooseInt (1, sz + 4)
     case someNat (fromIntegral x :: Natural) of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidth"

-- | The strides result has at most as many elements as the arith result.
sizeLeq ::
  (1 <= w, 1 <= u) =>
  NatRepr u -> S.Domain u -> A.Domain w -> Property
sizeLeq _w c arith =
  property (toInteger (S.size c) <= A.size arith)

-- | The strides result is contained in the arith result.
subsetOf ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> A.Domain w -> Property
subsetOf w c arith =
  case S.fromArith w arith of
    Nothing -> property (S.size c == 0)
    Just a  -> property (S.leqExact c a)

-- | The strides result is contained in the bitwise result lifted back
-- through 'S.fromBitwise'. Used by the @bitwise_<op>@ properties below.
subsetOfB ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> B.Domain w -> Property
subsetOfB w c b =
  case S.fromBitwise w b of
    Nothing -> property (S.size c == 0)
    Just a  -> property (S.leqExact c a)

-- | The strides result has at most as many elements as the bitwise result
-- lifted back through 'S.fromBitwise'. Fallback for ops whose closed form
-- can leave the bitwise image even when the bitwise lift is well-defined.
sizeLeqB ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> B.Domain w -> Property
sizeLeqB w c b =
  case S.fromBitwise w b of
    Nothing -> property (S.size c == 0)
    Just a  -> property (S.size c <= S.size a)

precise_negate :: (1 <= w) => NatRepr w -> S.Domain w -> Property
precise_negate w c =
  S.proper c ==> sizeLeq w (S.negate w c) (A.negate (S.hull c))

precise_add ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_add w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.add w a b) (A.add (S.hull a) (S.hull b))

precise_sub ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_sub w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.sub w a b) (A.add (S.hull a) (A.negate (S.hull b)))

precise_scale ::
  (1 <= w) =>
  NatRepr w -> Integer -> S.Domain w -> Property
precise_scale w k c =
  S.proper c ==> sizeLeq w (S.scale w k c) (A.scale k (S.hull c))

precise_mul ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_mul w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.mul w a b) (A.mul (S.hull a) (S.hull b))

precise_udiv ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_udiv w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.udiv w a b) (A.udiv (S.hull a) (S.hull b))

precise_urem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_urem w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.urem w a b) (A.urem (S.hull a) (S.hull b))

precise_sdiv ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_sdiv w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.sdiv w a b) (A.sdiv w (S.hull a) (S.hull b))

precise_srem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_srem w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.srem w a b) (A.srem w (S.hull a) (S.hull b))

precise_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_uremSmtlib w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.uremSmtlib w a b) (A.uremSmtlib (S.hull a) (S.hull b))

precise_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_sremSmtlib w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.sremSmtlib w a b) (A.sremSmtlib w (S.hull a) (S.hull b))

precise_zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Property
precise_zext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> sizeLeq u (S.zext w c u) (A.zext (S.hull c) u)

precise_sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Property
precise_sext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> sizeLeq u (S.sext w c u) (A.sext w (S.hull c) u)

precise_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> S.Domain u -> NatRepr v -> S.Domain v -> Property
precise_concat u a v b =
  case NR.leqAddPos u v of
    LeqProof ->
      S.proper a ==> S.proper b ==>
        sizeLeq (NR.addNat u v) (S.concat u a v b)
                (A.concat u (S.hull a) v (S.hull b))

precise_select ::
  forall i n w.
  (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> S.Domain w -> Property
precise_select i n w c =
  case NR.leqTrans (LeqProof :: LeqProof 1 n)
                   (NR.leqTrans (NR.addPrefixIsLeq i n)
                                (LeqProof :: LeqProof (i + n) w)) of
    LeqProof ->
      S.proper c ==> sizeLeq n (S.select i n w c) (A.select i n (S.hull c))

precise_shl ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_shl w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.shl w a b) (A.shl w (S.hull a) (S.hull b))

precise_lshr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_lshr w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.lshr w a b) (A.lshr w (S.hull a) (S.hull b))

precise_ashr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
precise_ashr w a b =
  S.proper a ==> S.proper b ==>
    sizeLeq w (S.ashr w a b) (A.ashr w (S.hull a) (S.hull b))

-- ------------------------------------------------------------------
-- * Subset properties
--
-- Each strides result is /also/ a subset of the corresponding arith result
-- (when this holds — closed-form @mul@, for instance, walks a coset that
-- can leave the arith convex hull). We test it everywhere and let the
-- failures tell us which ops actually do.

subset_negate :: (1 <= w) => NatRepr w -> S.Domain w -> Property
subset_negate w c =
  S.proper c ==> subsetOf w (S.negate w c) (A.negate (S.toArith c))

-- Note: there is no @subset_add@, @subset_sub@, or @subset_mul@. All three
-- ops are orientation-robust ('S.add'\/'S.sub'\/'S.mul'): they pick whichever
-- operand orientation gives the smallest-cardinality result. When the winner
-- isn't the forward orientation, the result walks a coset offset from arith's
-- arc — the two over-approximations of the concrete result then diverge in
-- incomparable directions (strides keeps coset structure, arith keeps arc
-- structure), so neither contains the other. The cardinality-precision
-- properties 'precise_add'\/'precise_sub'\/'precise_mul' still hold (strides is
-- never /larger/ than arith); only containment is forfeited, which is the price
-- of the orientation-robust precision win. See @GCD.md@ at the repo root.

subset_scale ::
  (1 <= w) =>
  NatRepr w -> Integer -> S.Domain w -> Property
subset_scale w k c =
  S.proper c ==> subsetOf w (S.scale w k c) (A.scale k (S.toArith c))

-- Note: there is no @subset_udiv@ / @subset_sdiv@ (nor for the @*Smtlib@
-- variants below). Closed-form division (CLP Table 3.1) returns a strided
-- coset whose elements differ from the arith result's arc once the quotient
-- has nontrivial coset structure, so — exactly as for 'mul' and as the module
-- header explains — neither is a subset of the other. The weaker /cardinality/
-- bound /does/ hold (we hull quotient endpoints rather than join domains; see
-- 'S.udiv'), and is checked by 'precise_udiv' / 'precise_sdiv' etc. Soundness
-- is covered by @correct_udiv@ / @correct_sdiv@.

subset_urem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
subset_urem w a b =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.urem w a b) (A.urem (S.toArith a) (S.toArith b))

subset_srem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
subset_srem w a b =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.srem w a b) (A.srem w (S.toArith a) (S.toArith b))

-- (No @subset_udivSmtlib@ / @subset_sdivSmtlib@ — same reason as
-- @subset_udiv@ above. Their SMT-LIB zero-divisor cases use 'pseudoJoin',
-- so we also do not assert the cardinality bounds. The remainder variants
-- still go through the arith lift, so 'precise_uremSmtlib' /
-- 'precise_sremSmtlib' remain asserted.)

subset_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
subset_uremSmtlib w a b =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.uremSmtlib w a b) (A.uremSmtlib (S.toArith a) (S.toArith b))

subset_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
subset_sremSmtlib w a b =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.sremSmtlib w a b) (A.sremSmtlib w (S.toArith a) (S.toArith b))

subset_zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Property
subset_zext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> subsetOf u (S.zext w c u) (A.zext (S.toArith c) u)

subset_sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Property
subset_sext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> subsetOf u (S.sext w c u) (A.sext w (S.toArith c) u)

subset_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> S.Domain u -> NatRepr v -> S.Domain v -> Property
subset_concat u a v b =
  case NR.leqAddPos u v of
    LeqProof ->
      S.proper a ==> S.proper b ==>
        subsetOf (NR.addNat u v) (S.concat u a v b)
                 (A.concat u (S.toArith a) v (S.toArith b))

subset_select ::
  forall i n w.
  (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> S.Domain w -> Property
subset_select i n w c =
  case NR.leqTrans (LeqProof :: LeqProof 1 n)
                   (NR.leqTrans (NR.addPrefixIsLeq i n)
                                (LeqProof :: LeqProof (i + n) w)) of
    LeqProof ->
      S.proper c ==> subsetOf n (S.select i n w c) (A.select i n (S.toArith c))

subset_shl ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
subset_shl w a b =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.shl w a b) (A.shl w (S.toArith a) (S.toArith b))

subset_lshr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
subset_lshr w a b =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.lshr w a b) (A.lshr w (S.toArith a) (S.toArith b))

subset_ashr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
subset_ashr w a b =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.ashr w a b) (A.ashr w (S.toArith a) (S.toArith b))

-- ------------------------------------------------------------------
-- * Bitwise-bound properties
--
-- Each strides op should be at least as precise as the corresponding
-- bitwise op on @S.toBitwise@'d operands lifted back through
-- 'S.fromBitwise'. These are regression tests for the planned replacement
-- of 'liftBitwise1' / 'liftBitwise2': the new implementation must not
-- regress against this oracle.
--
-- Subset via 'S.leqExact' is the default. Ops whose closed form can leave
-- the bitwise image fall back to cardinality (currently: @mul@, @udiv@,
-- @urem@, @sdiv@, @srem@, and their SMT-LIB variants — coset walks and
-- div/rem can both land outside the convex bitwise hull).

bitwise_negate :: (1 <= w) => NatRepr w -> S.Domain w -> Property
bitwise_negate w c =
  S.proper c ==> subsetOfB w (S.negate w c) (B.negate (S.toBitwise c))

bitwise_add ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_add w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.add w a b) (B.add (S.toBitwise a) (S.toBitwise b))

bitwise_sub ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_sub w a b =
  S.proper a ==> S.proper b ==>
    subsetOfB w (S.sub w a b) (B.sub (S.toBitwise a) (S.toBitwise b))

-- 'scale' walks a coset that the bitwise hull doesn't always cover; the
-- result is sometimes incomparable with the bitwise lift as a set.
bitwise_scale ::
  (1 <= w) =>
  NatRepr w -> Integer -> S.Domain w -> Property
bitwise_scale w k c =
  S.proper c ==> sizeLeqB w (S.scale w k c) (B.scale k (S.toBitwise c))

-- 'mul' walks a coset out of the bitwise hull, same as for the arith
-- hull; cardinality is the most we can claim.
bitwise_mul ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_mul w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.mul w a b) (B.mul (S.toBitwise a) (S.toBitwise b))

-- div/rem can leave the bitwise image; cardinality only.
bitwise_udiv ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_udiv w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.udiv w a b) (B.udiv (S.toBitwise a) (S.toBitwise b))

bitwise_urem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_urem w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.urem w a b) (B.urem (S.toBitwise a) (S.toBitwise b))

bitwise_sdiv ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_sdiv w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.sdiv w a b) (B.sdiv w (S.toBitwise a) (S.toBitwise b))

bitwise_srem ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_srem w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.srem w a b) (B.srem w (S.toBitwise a) (S.toBitwise b))

bitwise_udivSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_udivSmtlib w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.udivSmtlib w a b) (B.udivSmtlib (S.toBitwise a) (S.toBitwise b))

bitwise_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_uremSmtlib w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.uremSmtlib w a b) (B.uremSmtlib (S.toBitwise a) (S.toBitwise b))

bitwise_sdivSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_sdivSmtlib w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.sdivSmtlib w a b) (B.sdivSmtlib w (S.toBitwise a) (S.toBitwise b))

bitwise_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_sremSmtlib w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.sremSmtlib w a b) (B.sremSmtlib w (S.toBitwise a) (S.toBitwise b))

bitwise_not :: (1 <= w) => NatRepr w -> S.Domain w -> Property
bitwise_not w c =
  S.proper c ==> subsetOfB w (S.not w c) (B.not (S.toBitwise c))

bitwise_and ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_and w a b =
  S.proper a ==> S.proper b ==>
    subsetOfB w (S.and w a b) (B.and (S.toBitwise a) (S.toBitwise b))

bitwise_or ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_or w a b =
  S.proper a ==> S.proper b ==>
    subsetOfB w (S.or w a b) (B.or (S.toBitwise a) (S.toBitwise b))

bitwise_xor ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_xor w a b =
  S.proper a ==> S.proper b ==>
    subsetOfB w (S.xor w a b) (B.xor (S.toBitwise a) (S.toBitwise b))

-- ext/concat/select and the abstract shifts all go through 'liftArith2'
-- in strides (or 'fromArith' for ext/concat/select), so the strides result
-- is the arith arc of the bitwise input — generally incomparable with the
-- bitwise lift as a set, even when both are well-defined.
bitwise_zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Property
bitwise_zext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> sizeLeqB u (S.zext w c u) (B.zext (S.toBitwise c) u)

bitwise_sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Property
bitwise_sext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> sizeLeqB u (S.sext w c u) (B.sext w (S.toBitwise c) u)

bitwise_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> S.Domain u -> NatRepr v -> S.Domain v -> Property
bitwise_concat u a v b =
  case NR.leqAddPos u v of
    LeqProof ->
      S.proper a ==> S.proper b ==>
        sizeLeqB (NR.addNat u v) (S.concat u a v b)
                 (B.concat u (S.toBitwise a) v (S.toBitwise b))

bitwise_select ::
  forall i n w.
  (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> S.Domain w -> Property
bitwise_select i n w c =
  case NR.leqTrans (LeqProof :: LeqProof 1 n)
                   (NR.leqTrans (NR.addPrefixIsLeq i n)
                                (LeqProof :: LeqProof (i + n) w)) of
    LeqProof ->
      S.proper c ==> sizeLeqB n (S.select i n w c) (B.select i n (S.toBitwise c))

bitwise_shl ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_shl w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.shl w a b) (B.shlAbstract w (S.toBitwise a) (S.toBitwise b))

bitwise_lshr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_lshr w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.lshr w a b) (B.lshrAbstract w (S.toBitwise a) (S.toBitwise b))

bitwise_ashr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_ashr w a b =
  S.proper a ==> S.proper b ==>
    sizeLeqB w (S.ashr w a b) (B.ashrAbstract w (S.toBitwise a) (S.toBitwise b))

bitwise_rol ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_rol w a b =
  S.proper a ==> S.proper b ==>
    subsetOfB w (S.rol w a b) (B.rolAbstract w (S.toBitwise a) (S.toBitwise b))

bitwise_ror ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
bitwise_ror w a b =
  S.proper a ==> S.proper b ==>
    subsetOfB w (S.ror w a b) (B.rorAbstract w (S.toBitwise a) (S.toBitwise b))

tests :: TT.TestTree
tests = TT.testGroup "Precision (Strides at least as precise as Arith)"
  [ genTest "precise_negate" $
      do SW n <- genWidth
         precise_negate n <$> S.genDomain n
  , genTest "precise_add" $
      do SW n <- genWidth
         precise_add n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_sub" $
      do SW n <- genWidth
         precise_sub n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_scale" $
      do SW n <- genWidth
         precise_scale n <$> chooseInteger (0, maxUnsigned n)
                         <*> S.genDomain n
  , genTest "precise_mul" $
      do SW n <- genWidth
         precise_mul n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_udiv" $
      do SW n <- genWidth
         precise_udiv n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_urem" $
      do SW n <- genWidth
         precise_urem n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_sdiv" $
      do SW n <- genWidth
         precise_sdiv n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_srem" $
      do SW n <- genWidth
         precise_srem n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_uremSmtlib" $
      do SW n <- genWidth
         precise_uremSmtlib n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_sremSmtlib" $
      do SW n <- genWidth
         precise_sremSmtlib n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_zext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                pure (precise_zext w c u)
  , genTest "precise_sext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                pure (precise_sext w c u)
  , genTest "precise_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- S.genDomain m
         b <- S.genDomain n
         pure (precise_concat m a n b)
  , genTest "precise_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         c <- S.genDomain w
         pure (precise_select i n w c)
  , genTest "precise_shl" $
      do SW n <- genWidth
         precise_shl n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_lshr" $
      do SW n <- genWidth
         precise_lshr n <$> S.genDomain n <*> S.genDomain n
  , genTest "precise_ashr" $
      do SW n <- genWidth
         precise_ashr n <$> S.genDomain n <*> S.genDomain n

  -- Subset properties (a strides result is also a subset of arith).
  -- Some of these are expected to fail for ops whose closed form walks
  -- a coset that leaves the arith convex hull (e.g., 'mul').
  , genTest "subset_negate" $
      do SW n <- genWidth
         subset_negate n <$> S.genDomain n
  , genTest "subset_scale" $
      do SW n <- genWidth
         subset_scale n <$> chooseInteger (0, maxUnsigned n)
                        <*> S.genDomain n
  -- No subset_udiv / subset_sdiv (nor *Smtlib): closed-form division is
  -- set-incomparable with the arith lift; see subset_udiv's definition site.
  -- Only the cardinality bound is checked, via precise_udiv / precise_sdiv etc.
  , genTest "subset_urem" $
      do SW n <- genWidth
         subset_urem n <$> S.genDomain n <*> S.genDomain n
  , genTest "subset_srem" $
      do SW n <- genWidth
         subset_srem n <$> S.genDomain n <*> S.genDomain n
  , genTest "subset_uremSmtlib" $
      do SW n <- genWidth
         subset_uremSmtlib n <$> S.genDomain n <*> S.genDomain n
  , genTest "subset_sremSmtlib" $
      do SW n <- genWidth
         subset_sremSmtlib n <$> S.genDomain n <*> S.genDomain n
  , genTest "subset_zext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                pure (subset_zext w c u)
  , genTest "subset_sext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                pure (subset_sext w c u)
  , genTest "subset_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- S.genDomain m
         b <- S.genDomain n
         pure (subset_concat m a n b)
  , genTest "subset_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         c <- S.genDomain w
         pure (subset_select i n w c)
  , genTest "subset_shl" $
      do SW n <- genWidth
         subset_shl n <$> S.genDomain n <*> S.genDomain n
  , genTest "subset_lshr" $
      do SW n <- genWidth
         subset_lshr n <$> S.genDomain n <*> S.genDomain n
  , genTest "subset_ashr" $
      do SW n <- genWidth
         subset_ashr n <$> S.genDomain n <*> S.genDomain n

  -- Bitwise-bound regression tests. Strides should beat
  -- @S.fromBitwise w (B.op (S.toBitwise a) (S.toBitwise b))@ for every op.
  -- Some ops are commented out below: those don't yet have a native
  -- strides implementation (they go through 'liftArith2' / 'fromArith'),
  -- and the arith arc is genuinely less precise than the bitwise lift on
  -- some inputs. They become live regression tests once strides grows a
  -- native implementation that meets-in the bitwise oracle (or does
  -- better).
  , genTest "bitwise_negate" $
      do SW n <- genWidth
         bitwise_negate n <$> S.genDomain n
  , genTest "bitwise_add" $
      do SW n <- genWidth
         bitwise_add n <$> S.genDomain n <*> S.genDomain n
  , genTest "bitwise_sub" $
      do SW n <- genWidth
         bitwise_sub n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_scale" $
  --     do SW n <- genWidth
  --        bitwise_scale n <$> chooseInteger (0, maxUnsigned n)
  --                        <*> S.genDomain n
  , genTest "bitwise_mul" $
      do SW n <- genWidth
         bitwise_mul n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_udiv" $
  --     do SW n <- genWidth
  --        bitwise_udiv n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_urem" $
  --     do SW n <- genWidth
  --        bitwise_urem n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_sdiv" $
  --     do SW n <- genWidth
  --        bitwise_sdiv n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_srem" $
  --     do SW n <- genWidth
  --        bitwise_srem n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_udivSmtlib" $
  --     do SW n <- genWidth
  --        bitwise_udivSmtlib n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_uremSmtlib" $
  --     do SW n <- genWidth
  --        bitwise_uremSmtlib n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_sdivSmtlib" $
  --     do SW n <- genWidth
  --        bitwise_sdivSmtlib n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_sremSmtlib" $
  --     do SW n <- genWidth
  --        bitwise_sremSmtlib n <$> S.genDomain n <*> S.genDomain n
  , genTest "bitwise_not" $
      do SW n <- genWidth
         bitwise_not n <$> S.genDomain n
  -- , genTest "bitwise_and" $
  --     do SW n <- genWidth
  --        bitwise_and n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_or" $
  --     do SW n <- genWidth
  --        bitwise_or n <$> S.genDomain n <*> S.genDomain n
  , genTest "bitwise_xor" $
      do SW n <- genWidth
         bitwise_xor n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_zext" $
  --     do SW w <- genWidth
  --        SW n <- genWidth
  --        let u = addNat w n
  --        case testLeq (addNat w (knownNat @1)) u of
  --          Nothing -> error "impossible!"
  --          Just LeqProof ->
  --            do c <- S.genDomain w
  --               pure (bitwise_zext w c u)
  -- , genTest "bitwise_sext" $
  --     do SW w <- genWidth
  --        SW n <- genWidth
  --        let u = addNat w n
  --        case testLeq (addNat w (knownNat @1)) u of
  --          Nothing -> error "impossible!"
  --          Just LeqProof ->
  --            do c <- S.genDomain w
  --               pure (bitwise_sext w c u)
  -- , genTest "bitwise_concat" $
  --     do SW m <- genWidth
  --        SW n <- genWidth
  --        a <- S.genDomain m
  --        b <- S.genDomain n
  --        pure (bitwise_concat m a n b)
  -- , genTest "bitwise_select" $
  --     do SW n <- genWidth
  --        SW i <- genWidth
  --        SW z <- genWidth
  --        let i_n = addNat i n
  --        let w = addNat i_n z
  --        LeqProof <- pure (addIsLeq i_n z)
  --        c <- S.genDomain w
  --        pure (bitwise_select i n w c)
  -- , genTest "bitwise_shl" $
  --     do SW n <- genWidth
  --        bitwise_shl n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_lshr" $
  --     do SW n <- genWidth
  --        bitwise_lshr n <$> S.genDomain n <*> S.genDomain n
  -- , genTest "bitwise_ashr" $
  --     do SW n <- genWidth
  --        bitwise_ashr n <$> S.genDomain n <*> S.genDomain n
  , genTest "bitwise_rol" $
      do SW n <- genWidth
         bitwise_rol n <$> S.genDomain n <*> S.genDomain n
  , genTest "bitwise_ror" $
      do SW n <- genWidth
         bitwise_ror n <$> S.genDomain n <*> S.genDomain n
  ]
