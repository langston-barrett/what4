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

-- @subset_zext@ holds because 'S.zext' is exact on non-wrapping orbits and
-- its forced-bits refinement is fed the arith arc's own (never-wrapping at
-- the wider width) bounds, so it can only shrink that arc.
subset_zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> S.Domain w -> NatRepr u -> Property
subset_zext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      S.proper c ==> subsetOf u (S.zext w c u) (A.zext (S.toArith c) u)

-- (No @subset_sext@ / @subset_concat@ / @subset_select@ — when the arith
-- arc wraps modulo the target width, the forced-bits refinement in these
-- conversions can return a progression that is smaller by cardinality but
-- not contained in the arith arc. The cardinality bounds are still
-- asserted by @precise_sext@ / @precise_concat@ / @precise_select@.)

-- These check the @*Raw@ kernel against the arith abstraction. The
-- 'S.psplitOp2R'-wrapped public versions ('S.lshr' etc.) can soundly land on
-- a coset that the arith arc does not contain — strides and arith are
-- /incomparable/ once 'pseudoJoin' enters the picture — so those are checked
-- against the concrete operation directly via 'correct_shl' / 'correct_lshr' /
-- 'correct_ashr' instead.
--
-- (No @subset_shl@ — 'S.shlRaw' keeps the mul-based candidate whenever it
-- is smaller by cardinality, even when it is not contained in the arith
-- arc. @precise_shl@ still asserts the cardinality bound.)
subset_lshr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
subset_lshr w a b =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.lshrRaw w a b) (A.lshr w (S.toArith a) (S.toArith b))

subset_ashr ::
  (1 <= w) =>
  NatRepr w -> S.Domain w -> S.Domain w -> Property
subset_ashr w a b =
  S.proper a ==> S.proper b ==>
    subsetOf w (S.ashrRaw w a b) (A.ashr w (S.toArith a) (S.toArith b))

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
  , genTest "subset_lshr" $
      do SW n <- genWidth
         subset_lshr n <$> S.genDomain n <*> S.genDomain n
  , genTest "subset_ashr" $
      do SW n <- genWidth
         subset_ashr n <$> S.genDomain n <*> S.genDomain n
  ]
