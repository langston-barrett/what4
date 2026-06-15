{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Strides (tests) where

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TT

import qualified Data.List as List
import           Data.Maybe (fromJust)
import           Data.Parameterized.NatRepr (NatRepr, addNat, addIsLeq, isPosNat, knownNat, someNat, testLeq, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import qualified What4.Domains.BV.Strides as S
import           What4.Domains.Verification (Gen, chooseInt, chooseInteger, getSize)
import           VerifyBindings (genTest)

import qualified Strides.Internal as Internal
import qualified Strides.Precision as Precision

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

-- | Like 'genWidth' but capped at 8, for tests that enumerate the full progression
-- (which can have up to @2^w@ elements for odd strides).
genWidthSmall :: Gen SomeWidth
genWidthSmall =
  do x <- chooseInt (1, 8)
     case someNat (fromIntegral x :: Natural) of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidthSmall"

-- | Capped at 5, for tests whose reference enumerates all @(stride, start, n)@
-- triples (@O(2^{3w})@), which is intractable past small widths.
genWidthTiny :: Gen SomeWidth
genWidthTiny =
  do x <- chooseInt (1, 5)
     case someNat (fromIntegral x :: Natural) of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidthTiny"

genNatBV :: NatRepr w -> Gen Natural
genNatBV w = fromInteger <$> chooseInteger (0, maxUnsigned w)

-- | A strictly-ascending list of distinct 'Natural's in @[0, 2^w)@.
genAscNatList :: NatRepr w -> Gen [Natural]
genAscNatList w =
  do sz <- getSize
     k <- chooseInt (0, min (sz + 1) 64)
     ys <- mapM (const (genNatBV w)) [1 .. k]
     pure (List.sort (List.nub ys))

-- | An arbitrary nonnegative natural, used to seed bitvector-shaped values
-- whose width is chosen separately by 'genWidthExp'.
genNat :: Gen Natural
genNat = fromInteger <$> chooseInteger (0, 2 ^ (64 :: Int))

-- | Width exponent @k@ in @[1, sz + 4]@, used by helpers that take @2^k@ as a
-- modulus directly rather than through a progression.
genWidthExp :: Gen Int
genWidthExp =
  do sz <- getSize
     chooseInt (1, sz + 4)

-- | An odd 'Natural' in @[0, 2^64)@, suitable as input to 'invModPow2'.
genOddNat :: Gen Natural
genOddNat = (\x -> x * 2 + 1) <$> genNat

tests :: TT.TestTree
tests = TT.testGroup "Strides"
  [ genTest "modNegCorrect" $
      S.modNegCorrect <$> genNat <*> genWidthExp
  , genTest "modSubCorrect" $
      S.modSubCorrect <$> genNat <*> genNat <*> genWidthExp
  , genTest "firstCosetMemberCorrect" $
      S.firstCosetMemberCorrect <$> genNat <*> genNat <*> genWidthExp <*> genWidthExp
  , genTest "wrapOffsetCorrect" $
      do SW n <- genWidth
         S.wrapOffsetCorrect <$> S.genDomain n <*> genNatBV n
  , genTest "strideGcdDividesStride" $
      do SW n <- genWidth
         S.strideGcdDividesStride <$> S.genDomain n
  , genTest "strideGcdIsPow2" $
      do SW n <- genWidth
         S.strideGcdIsPow2 <$> S.genDomain n
  , genTest "orbitLenViaToList" $
      do SW n <- genWidthSmall
         S.orbitLenViaToList <$> S.genDomain n
  , genTest "divByPow2Correct" $
      S.divByPow2Correct <$> genNat <*> genWidthExp
  , genTest "invModPow2Correct" $
      S.invModPow2Correct <$> genOddNat <*> genWidthExp
  , genTest "floorSumCorrect" $
      S.floorSumCorrect <$> genNat <*> genNat <*> genNat <*> genNat
  , genTest "valueIndexCorrect" $
      do SW n <- genWidth
         S.valueIndexCorrect <$> S.genDomain n <*> genNatBV n
  , genTest "valueIndexMaybeCorrect" $
      do SW n <- genWidth
         S.valueIndexMaybeCorrect <$> S.genDomain n <*> genNatBV n
  , genTest "valueAtCorrect" $
      do SW n <- genWidth
         S.valueAtCorrect <$> S.genDomain n <*> genNatBV n
  , genTest "circLeqAtZero" $
      S.circLeqAtZero <$> genNat <*> genNat <*> genWidthExp
  , genTest "circLeqAnchorMin" $
      S.circLeqAnchorMin <$> genNat <*> genNat <*> genWidthExp
  , genTest "circLeqAnchorMax" $
      S.circLeqAnchorMax <$> genNat <*> genNat <*> genWidthExp
  , genTest "isSelfWrappingViaToList" $
      do SW n <- genWidthSmall
         S.isSelfWrappingViaToList <$> S.genDomain n
  , genTest "startMember" $
      do SW n <- genWidth
         S.startMember <$> S.genDomain n
  , genTest "endMember" $
      do SW n <- genWidth
         S.endMember <$> S.genDomain n
  , genTest "toListMember" $
      do SW n <- genWidthSmall
         S.toListMember <$> S.genDomain n
  , genTest "memberToList" $
      do SW n <- genWidthSmall
         S.memberToList <$> S.genDomain n <*> genNatBV n
  , genTest "memberArcCorrect" $
      do SW n <- genWidth
         S.memberArcCorrect <$> S.genDomain n <*> genNatBV n
  , genTest "containsZeroCorrect" $
      do SW n <- genWidth
         S.containsZeroCorrect <$> S.genDomain n
  , genTest "toListNoDuplicates" $
      do SW n <- genWidthSmall
         S.toListNoDuplicates <$> S.genDomain n
  , genTest "leqCorrect" $
      do SW n <- genWidthSmall
         S.leqCorrect <$> S.genDomain n <*> S.genDomain n
  , genTest "leqReflexive" $
      do SW n <- genWidth
         S.leqReflexive <$> S.genDomain n
  , genTest "leqTransitive" $
      do SW n <- genWidth
         S.leqTransitive <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "leqRefinesLeqExact" $
      do SW n <- genWidthSmall
         S.leqRefinesLeqExact <$> S.genDomain n <*> S.genDomain n
  , genTest "leqPreciseCorrect" $
      do SW n <- genWidthSmall
         S.leqPreciseCorrect <$> S.genDomain n <*> S.genDomain n
  , genTest "leqPreciseReflexive" $
      do SW n <- genWidth
         S.leqPreciseReflexive <$> S.genDomain n
  , genTest "leqPreciseRefinesLeqExact" $
      do SW n <- genWidthSmall
         S.leqPreciseRefinesLeqExact <$> S.genDomain n <*> S.genDomain n
  , genTest "leqExactCorrect" $
      do SW n <- genWidthSmall
         S.leqExactCorrect <$> S.genDomain n <*> S.genDomain n
  , genTest "leqExactComplete" $
      do SW n <- genWidthSmall
         S.leqExactComplete <$> S.genDomain n <*> S.genDomain n
  , genTest "leqExactReflexive" $
      do SW n <- genWidth
         S.leqExactReflexive <$> S.genDomain n
  , genTest "leqExactTransitive" $
      do SW n <- genWidth
         S.leqExactTransitive <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "leqExactPartialAgrees" $
      do SW n <- genWidth
         S.leqExactPartialAgrees <$> S.genDomain n <*> S.genDomain n
  , genTest "leqExactWindowAgrees" $
      do SW n <- genWidth
         S.leqExactWindowAgrees <$> S.genDomain n <*> S.genDomain n
  , genTest "sizeViaToList" $
      do SW n <- genWidthSmall
         S.sizeViaToList <$> S.genDomain n
  , genTest "cosetsDisjointCorrect" $
      do SW n <- genWidth
         S.cosetsDisjointCorrect <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "eqExactCorrect" $
      do SW n <- genWidthSmall
         S.eqExactCorrect <$> S.genDomain n <*> S.genDomain n
  , genTest "eqExactReflexive" $
      do SW n <- genWidth
         S.eqExactReflexive <$> S.genDomain n
  , genTest "eqExactSymmetric" $
      do SW n <- genWidth
         S.eqExactSymmetric <$> S.genDomain n <*> S.genDomain n
  , genTest "eqExactTransitive" $
      do SW n <- genWidth
         S.eqExactTransitive <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "canonLossless" $
      do SW n <- genWidthSmall
         S.canonLossless <$> S.genDomain n
  , genTest "canonProper" $
      do SW n <- genWidth
         S.canonProper <$> S.genDomain n
  , genTest "canonUnique" $
      do SW n <- genWidthSmall
         S.canonUnique <$> S.genDomain n <*> S.genDomain n
  , genTest "canonIdempotent" $
      do SW n <- genWidth
         S.canonIdempotent <$> S.genDomain n
  , genTest "eqCorrect" $
      do SW n <- genWidthSmall
         S.eqCorrect <$> S.genDomain n <*> S.genDomain n
  , genTest "canonForwardOriented" $
      do SW n <- genWidth
         S.canonForwardOriented <$> S.genDomain n
  -- Reference enumerates all (stride, start, n) triples, so cap the width.
  , genTest "canonMatchesSearch" $
      do SW n <- genWidthTiny
         S.canonMatchesSearch n <$> S.genDomain n
  , genTest "canonHashRespectsEq" $
      do SW n <- genWidth
         S.canonHashRespectsEq <$> S.genDomain n <*> S.genDomain n
  , genTest "toArithCorrect" $
      do SW n <- genWidth
         S.toArithCorrect n <$> S.genDomain n <*> genNatBV n
  , genTest "startEndArcCorrect" $
      do SW n <- genWidth
         S.startEndArcCorrect n <$> S.genDomain n <*> genNatBV n
  , genTest "cosetArcCorrect" $
      do SW n <- genWidth
         S.cosetArcCorrect n <$> S.genDomain n <*> genNatBV n
  , genTest "fromArithCorrect" $
      do SW n <- genWidth
         S.fromArithCorrect n <$> A.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "roundtripArith" $
      do SW n <- genWidth
         S.roundtripArith n <$> A.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "toBitwiseCorrect" $
      do SW n <- genWidth
         S.toBitwiseCorrect n <$> S.genDomain n <*> genNatBV n
  , genTest "strideBitwiseCorrect" $
      do SW n <- genWidth
         S.strideBitwiseCorrect n <$> S.genDomain n <*> genNatBV n
  , genTest "forcedBitsDisjoint" $
      do SW n <- genWidth
         S.forcedBitsDisjoint <$> S.genDomain n
  , genTest "forcedBitsMember" $
      do SW n <- genWidth
         S.forcedBitsMember <$> S.genDomain n <*> genNatBV n
  , genTest "nextAgreeingCorrect" $
      do SW n <- genWidth
         S.nextAgreeingCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n <*> genNatBV n
  , genTest "prevAgreeingCorrect" $
      do SW n <- genWidth
         S.prevAgreeingCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n <*> genNatBV n
  , genTest "arcExtremesCorrect" $
      do SW n <- genWidth
         S.arcExtremesCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n
           <*> genNatBV n <*> genNatBV n
  , genTest "fromForcedBitsArcCorrect" $
      do SW n <- genWidth
         S.fromForcedBitsArcCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n
           <*> genNatBV n <*> genNatBV n
  , genTest "fromForcedCorrect" $
      do SW n <- genWidth
         S.fromForcedCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n
  , genTest "fromForcedBitsCorrect" $
      do SW n <- genWidth
         S.fromForcedBitsCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n
           <*> genNatBV n <*> genNatBV n
  , genTest "fromForcedBitsSignedCorrect" $
      do SW n <- genWidth
         S.fromForcedBitsSignedCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n
           <*> genNatBV n <*> genNatBV n
  , genTest "fromBitwiseCorrect" $
      do SW n <- genWidth
         S.fromBitwiseCorrect n <$> B.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "fromAscEltListMember" $
      do SW n <- genWidth
         S.fromAscEltListMember n <$> genAscNatList n
  , genTest "fromAscEltListToListExactNonWrapping" $
      do SW n <- genWidthSmall
         S.fromAscEltListToListExactNonWrapping n <$> S.genDomain n

  -- Arithmetic
  , genTest "correct_neg" $
      do SW n <- genWidth
         (\c x -> S.correct_neg n c x) <$> S.genDomain n <*> genNatBV n
  , genTest "reverseDSameSet" $
      do SW n <- genWidthSmall
         S.reverseDSameSet n <$> S.genDomain n
  , genTest "psplitProper" $
      do SW n <- genWidth
         S.psplitProper n <$> S.genDomain n
  , genTest "psplitCovers" $
      do SW n <- genWidthSmall
         S.psplitCovers n <$> S.genDomain n
  , genTest "psplitPartitions" $
      do SW n <- genWidthSmall
         S.psplitPartitions n <$> S.genDomain n
  , genTest "psplitOp2Sound" $
      do SW n <- genWidth
         S.psplitOp2Sound n <$> S.genDomain n <*> genNatBV n
                            <*> S.genDomain n <*> genNatBV n
  , genTest "correct_add" $
      do SW n <- genWidth
         S.correct_add n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "addRobustDominatesRaw" $
      do SW n <- genWidth
         S.addRobustDominatesRaw n <$> S.genDomain n <*> S.genDomain n
  , genTest "addSubSizeCorrect" $
      do SW n <- genWidth
         S.addSubSizeCorrect n <$> S.genDomain n <*> S.genDomain n
  , genTest "addRobustClosedFormAgrees" $
      do SW n <- genWidth
         S.addRobustClosedFormAgrees n <$> S.genDomain n <*> S.genDomain n
  , genTest "correct_sub" $
      do SW n <- genWidth
         S.correct_sub n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "subRobustDominatesRaw" $
      do SW n <- genWidth
         S.subRobustDominatesRaw n <$> S.genDomain n <*> S.genDomain n
  , genTest "correct_scale" $
      do SW n <- genWidth
         S.correct_scale n <$> chooseInteger (0, maxUnsigned n)
                           <*> S.genDomain n <*> genNatBV n
  , genTest "correct_mul" $
      do SW n <- genWidth
         S.correct_mul n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "mulRobustDominatesRaw" $
      do SW n <- genWidth
         S.mulRobustDominatesRaw n <$> S.genDomain n <*> S.genDomain n
  , genTest "correct_mulCorners" $
      do SW n <- genWidth
         S.correct_mulCorners n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_mulNoStraddleU" $
      do SW n <- genWidth
         S.correct_mulNoStraddleU n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_mulNoStraddleS" $
      do SW n <- genWidth
         S.correct_mulNoStraddleS n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_scaleSingleton" $
      do SW n <- genWidth
         S.correct_scaleSingleton n <$> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "zboundsArcSameModular" $
      do SW n <- genWidth
         S.zboundsArcSameModular <$> S.genDomain n
  , genTest "zboundsArcMinMidpoint" $
      do SW n <- genWidth
         S.zboundsArcMinMidpoint <$> S.genDomain n
  , genTest "cornerArcEncloses" $
      do SW n <- genWidth
         S.cornerArcEncloses <$> S.genDomain n <*> S.genDomain n <*> genNatBV n <*> genNatBV n
  , genTest "cornerProductStrideDivides" $
      do SW n <- genWidth
         S.cornerProductStrideDivides <$> S.genDomain n <*> S.genDomain n <*> genNatBV n <*> genNatBV n
  , genTest "clpStepBoundSound" $
      do SW n <- genWidth
         S.clpStepBoundSound <$> S.genDomain n <*> S.genDomain n <*> genNatBV n <*> genNatBV n
  , genTest "arcStepBoundSound" $
      do SW n <- genWidth
         S.arcStepBoundSound <$> S.genDomain n <*> S.genDomain n <*> genNatBV n <*> genNatBV n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         S.correct_udiv n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_urem" $
      do SW n <- genWidth
         S.correct_urem n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         S.correct_sdiv n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_srem" $
      do SW n <- genWidth
         S.correct_srem n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n

  -- Exactness
  , genTest "addExact" $
      do SW n <- genWidthSmall
         S.addExact n <$> S.genDomain n <*> S.genDomain n
  , genTest "subExact" $
      do SW n <- genWidthSmall
         S.subExact n <$> S.genDomain n <*> S.genDomain n
  , genTest "mulConstExact" $
      do SW n <- genWidthSmall
         S.mulConstExact n <$> genNatBV n <*> S.genDomain n
  , genTest "udivConstExact" $
      do SW n <- genWidthSmall
         S.udivConstExact n <$> genNatBV n <*> S.genDomain n
  , genTest "uremConstExact" $
      do SW n <- genWidthSmall
         S.uremConstExact n <$> genNatBV n <*> S.genDomain n
  , genTest "ultExactTrueSeparated" $
      do SW n <- genWidthSmall
         S.ultExactTrueSeparated n <$> S.genDomain n <*> S.genDomain n
  , genTest "ultExactFalseSeparated" $
      do SW n <- genWidthSmall
         S.ultExactFalseSeparated n <$> S.genDomain n <*> S.genDomain n

  , genTest "correct_udivSmtlib" $
      do SW n <- genWidth
         S.correct_udivSmtlib n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_uremSmtlib" $
      do SW n <- genWidth
         S.correct_uremSmtlib n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_sdivSmtlib" $
      do SW n <- genWidth
         S.correct_sdivSmtlib n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_sremSmtlib" $
      do SW n <- genWidth
         S.correct_sremSmtlib n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n

  -- Bitwise
  , genTest "correct_not" $
      do SW n <- genWidth
         (\c x -> S.correct_not n c x) <$> S.genDomain n <*> genNatBV n
  , genTest "correct_and" $
      do SW n <- genWidth
         S.correct_and n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_or" $
      do SW n <- genWidth
         S.correct_or n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_xor" $
      do SW n <- genWidth
         S.correct_xor n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_andPrecise" $
      do SW n <- genWidth
         S.correct_andPrecise n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_orPrecise" $
      do SW n <- genWidth
         S.correct_orPrecise n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_andSingleton" $
      do SW n <- genWidth
         S.correct_andSingleton n <$> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "warrenAndLoCorrect" $
      S.warrenAndLoCorrect <$> genNat <*> genNat <*> genNat <*> genNat
                           <*> genNat <*> genNat <*> genWidthExp
  , genTest "warrenAndHiCorrect" $
      S.warrenAndHiCorrect <$> genNat <*> genNat <*> genNat <*> genNat
                           <*> genNat <*> genNat <*> genWidthExp
  , genTest "operandRangeCorrect" $
      do SW n <- genWidth
         S.operandRangeCorrect <$> S.genDomain n <*> genNatBV n
  , genTest "andPreciseDominatesAndFast" $
      do SW n <- genWidth
         S.andPreciseDominatesAndFast n <$> S.genDomain n <*> S.genDomain n

  -- Concatenation, extension, selection, and truncation
  , genTest "correct_zero_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                x <- genNatBV w
                pure (S.correct_zero_ext w c u x)
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- S.genDomain w
                x <- genNatBV w
                pure (S.correct_sign_ext w c u x)
  , genTest "correct_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- S.genDomain m
         x <- genNatBV m
         b <- S.genDomain n
         y <- genNatBV n
         pure (S.correct_concat m a x n b y)
  , genTest "correct_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         c <- S.genDomain w
         x <- genNatBV w
         pure (S.correct_select i n w c x)

  -- Shifts and rotations
  , genTest "correct_shl" $
      do SW n <- genWidth
         S.correct_shl n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_lshr" $
      do SW n <- genWidth
         S.correct_lshr n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_ashr" $
      do SW n <- genWidth
         S.correct_ashr n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_rol" $
      do SW n <- genWidth
         S.correct_rol n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_rolPrecise" $
      do SW n <- genWidth
         S.correct_rolPrecise n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "rolPreciseRawDominatesRolRaw" $
      do SW n <- genWidth
         S.rolPreciseRawDominatesRolRaw n <$> S.genDomain n <*> S.genDomain n
  , genTest "correct_ror" $
      do SW n <- genWidth
         S.correct_ror n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_rorPrecise" $
      do SW n <- genWidth
         S.correct_rorPrecise n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "rorPreciseRawDominatesRorRaw" $
      do SW n <- genWidth
         S.rorPreciseRawDominatesRorRaw n <$> S.genDomain n <*> S.genDomain n

  -- Lattice operations
  , genTest "correct_pseudoMeet" $
      do SW n <- genWidth
         S.correct_pseudoMeet n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_pseudoMeetPrecise" $
      do SW n <- genWidth
         S.correct_pseudoMeetPrecise n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "pseudoMeetLowerBound" $
      do SW n <- genWidth
         S.pseudoMeetLowerBound n <$> S.genDomain n <*> S.genDomain n
  , genTest "pseudoMeetPreciseLowerBound" $
      do SW n <- genWidth
         S.pseudoMeetPreciseLowerBound n <$> S.genDomain n <*> S.genDomain n
  , genTest "pseudoMeetCommutative" $
      do SW n <- genWidth
         S.pseudoMeetCommutative n <$> S.genDomain n <*> S.genDomain n
  , genTest "pseudoMeetPreciseCommutative" $
      do SW n <- genWidth
         S.pseudoMeetPreciseCommutative n <$> S.genDomain n <*> S.genDomain n
  , genTest "pseudoMeetIdempotent" $
      do SW n <- genWidth
         S.pseudoMeetIdempotent n <$> S.genDomain n
  , genTest "pseudoMeetPreciseIdempotent" $
      do SW n <- genWidth
         S.pseudoMeetPreciseIdempotent n <$> S.genDomain n
  , genTest "nsplitUnion" $
      do SW n <- genWidth
         S.nsplitUnion n <$> S.genDomain n <*> genNatBV n
  , genTest "nsplitDisjoint" $
      do SW n <- genWidth
         S.nsplitDisjoint n <$> S.genDomain n <*> genNatBV n
  , genTest "ssplitUnion" $
      do SW n <- genWidth
         S.ssplitUnion n <$> S.genDomain n <*> genNatBV n
  , genTest "ssplitDisjoint" $
      do SW n <- genWidth
         S.ssplitDisjoint n <$> S.genDomain n <*> genNatBV n
  , genTest "correct_pseudoJoin" $
      do SW n <- genWidth
         S.correct_pseudoJoin n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_pseudoJoinPrecise" $
      do SW n <- genWidth
         S.correct_pseudoJoinPrecise n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "pseudoJoinUpperBound" $
      do SW n <- genWidth
         S.pseudoJoinUpperBound n <$> S.genDomain n <*> S.genDomain n
  , genTest "pseudoJoinPreciseUpperBound" $
      do SW n <- genWidth
         S.pseudoJoinPreciseUpperBound n <$> S.genDomain n <*> S.genDomain n
  , genTest "pseudoJoinCommutative" $
      do SW n <- genWidth
         S.pseudoJoinCommutative n <$> S.genDomain n <*> S.genDomain n
  , genTest "pseudoJoinPreciseCommutative" $
      do SW n <- genWidth
         S.pseudoJoinPreciseCommutative n <$> S.genDomain n <*> S.genDomain n
  , genTest "pseudoJoinIdempotent" $
      do SW n <- genWidth
         S.pseudoJoinIdempotent n <$> S.genDomain n
  , genTest "pseudoJoinPreciseIdempotent" $
      do SW n <- genWidth
         S.pseudoJoinPreciseIdempotent n <$> S.genDomain n
  , genTest "pseudoJoinPreciseRefinesJoin" $
      do SW n <- genWidth
         S.pseudoJoinPreciseRefinesJoin n <$> S.genDomain n <*> S.genDomain n
  , genTest "pseudoJoinMinimalUpperBound" $
      do SW n <- genWidth
         S.pseudoJoinMinimalUpperBound n <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "pseudoJoinPreciseMinimalUpperBound" $
      do SW n <- genWidth
         S.pseudoJoinPreciseMinimalUpperBound n <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "boundingBoxJoinMinimalUpperBound" $
      do SW n <- genWidth
         S.boundingBoxJoinMinimalUpperBound n <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "pseudoMeetMaximalLowerBound" $
      do SW n <- genWidth
         S.pseudoMeetMaximalLowerBound n <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "pseudoMeetPreciseMaximalLowerBound" $
      do SW n <- genWidth
         S.pseudoMeetPreciseMaximalLowerBound n <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "lowerBoundMaximalAmongCandidates" $
      do SW n <- genWidth
         S.lowerBoundMaximalAmongCandidates n <$> S.genDomain n <*> S.genDomain n
  , genTest "pseudoMeetTopIdentity" $
      do SW n <- genWidth
         S.pseudoMeetTopIdentity n <$> S.genDomain n
  , genTest "pseudoMeetPreciseTopIdentity" $
      do SW n <- genWidth
         S.pseudoMeetPreciseTopIdentity n <$> S.genDomain n
  , genTest "pseudoJoinTopAnnihilator" $
      do SW n <- genWidth
         S.pseudoJoinTopAnnihilator n <$> S.genDomain n
  , genTest "pseudoJoinPreciseTopAnnihilator" $
      do SW n <- genWidth
         S.pseudoJoinPreciseTopAnnihilator n <$> S.genDomain n
  , genTest "correct_boundingBoxJoin" $
      do SW n <- genWidth
         S.correct_boundingBoxJoin n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "boundingBoxJoinCommutative" $
      do SW n <- genWidth
         S.boundingBoxJoinCommutative n <$> S.genDomain n <*> S.genDomain n
  , genTest "boundingBoxJoinIdempotent" $
      do SW n <- genWidth
         S.boundingBoxJoinIdempotent n <$> S.genDomain n
  , genTest "boundingBoxJoinTopAnnihilator" $
      do SW n <- genWidth
         S.boundingBoxJoinTopAnnihilator n <$> S.genDomain n
  , genTest "boundingBoxJoinUpperBound" $
      do SW n <- genWidth
         S.boundingBoxJoinUpperBound n <$> S.genDomain n <*> S.genDomain n
  , genTest "boundingBoxJoinAssociative" $
      do SW n <- genWidth
         S.boundingBoxJoinAssociative n <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "boundingBoxJoinMonotone" $
      do SW n <- genWidth
         S.boundingBoxJoinMonotone n <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "pseudoJoinDominatesBoundingBoxJoin" $
      do SW n <- genWidth
         S.pseudoJoinDominatesBoundingBoxJoin n <$> S.genDomain n <*> S.genDomain n
  , genTest "correct_exactJoin" $
      do SW n <- genWidth
         S.correct_exactJoin n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "exactJoinCommutative" $
      do SW n <- genWidth
         S.exactJoinCommutative n <$> S.genDomain n <*> S.genDomain n
  , genTest "exactJoinIdempotent" $
      do SW n <- genWidth
         S.exactJoinIdempotent n <$> S.genDomain n
  , genTest "exactJoinUpperBound" $
      do SW n <- genWidth
         S.exactJoinUpperBound n <$> S.genDomain n <*> S.genDomain n
  , genTest "exactJoinTopAnnihilator" $
      do SW n <- genWidth
         S.exactJoinTopAnnihilator n <$> S.genDomain n
  , genTest "exactJoinAssociative" $
      do SW n <- genWidth
         S.exactJoinAssociative n <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "correct_exactMeet" $
      do SW n <- genWidth
         S.correct_exactMeet n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "exactMeetCommutative" $
      do SW n <- genWidth
         S.exactMeetCommutative n <$> S.genDomain n <*> S.genDomain n
  , genTest "exactMeetIdempotent" $
      do SW n <- genWidth
         S.exactMeetIdempotent n <$> S.genDomain n
  , genTest "exactMeetLowerBound" $
      do SW n <- genWidth
         S.exactMeetLowerBound n <$> S.genDomain n <*> S.genDomain n
  , genTest "exactMeetTopIdentity" $
      do SW n <- genWidth
         S.exactMeetTopIdentity n <$> S.genDomain n
  , genTest "exactMeetAssociative" $
      do SW n <- genWidth
         S.exactMeetAssociative n <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "lowerBoundDominatedByPseudoMeet" $
      do SW n <- genWidth
         S.lowerBoundDominatedByPseudoMeet n <$> S.genDomain n <*> S.genDomain n
  , genTest "correct_lowerBound" $
      do SW n <- genWidth
         S.correct_lowerBound n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "lowerBoundLeqExactBoth" $
      do SW n <- genWidth
         S.lowerBoundLeqExactBoth n <$> S.genDomain n <*> S.genDomain n
  , genTest "lowerBoundCommutative" $
      do SW n <- genWidth
         S.lowerBoundCommutative n <$> S.genDomain n <*> S.genDomain n
  , genTest "lowerBoundIdempotent" $
      do SW n <- genWidth
         S.lowerBoundIdempotent n <$> S.genDomain n
  , genTest "lowerBoundTopIdentity" $
      do SW n <- genWidth
         S.lowerBoundTopIdentity n <$> S.genDomain n
  , genTest "lowerBoundIsLargestLowerBound" $
      do SW n <- genWidth
         S.lowerBoundIsLargestLowerBound n <$> S.genDomain n <*> S.genDomain n
  , genTest "correct_lowerBounds" $
      do SW n <- genWidth
         S.correct_lowerBounds n <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "lowerBoundsAllSubsets" $
      do SW n <- genWidth
         S.lowerBoundsAllSubsets n <$> S.genDomain n <*> S.genDomain n
  -- Uses 'toList' to compare element sets, so capped at small widths.
  , genTest "correct_compactify" $
      do SW n <- genWidthSmall
         k <- chooseInt (0, 4)
         cs <- mapM (const (S.genDomain n)) [1 .. k]
         pure (S.correct_compactify n cs)
  , genTest "trimSelfWrapNotSelfWrapping" $
      do SW n <- genWidth
         S.trimSelfWrapNotSelfWrapping n <$> S.genDomain n
  , genTest "trimSelfWrapSubset" $
      do SW n <- genWidth
         S.trimSelfWrapSubset n <$> S.genDomain n
  , genTest "trimSelfWrapIdentity" $
      do SW n <- genWidth
         S.trimSelfWrapIdentity n <$> S.genDomain n
  , genTest "trimSelfWrapIdempotent" $
      do SW n <- genWidth
         S.trimSelfWrapIdempotent n <$> S.genDomain n

  -- Branch-condition assumptions
  , genTest "correct_assumeUlt" $
      do SW n <- genWidth
         S.correct_assumeUlt n <$> S.genDomain n <*> genNatBV n
                               <*> S.genDomain n <*> genNatBV n
  , genTest "correct_assumeUle" $
      do SW n <- genWidth
         S.correct_assumeUle n <$> S.genDomain n <*> genNatBV n
                               <*> S.genDomain n <*> genNatBV n
  , genTest "correct_assumeUgt" $
      do SW n <- genWidth
         S.correct_assumeUgt n <$> S.genDomain n <*> genNatBV n
                               <*> S.genDomain n <*> genNatBV n
  , genTest "correct_assumeUge" $
      do SW n <- genWidth
         S.correct_assumeUge n <$> S.genDomain n <*> genNatBV n
                               <*> S.genDomain n <*> genNatBV n
  , genTest "correct_assumeSlt" $
      do SW n <- genWidth
         S.correct_assumeSlt n <$> S.genDomain n <*> genNatBV n
                               <*> S.genDomain n <*> genNatBV n
  , genTest "correct_assumeSle" $
      do SW n <- genWidth
         S.correct_assumeSle n <$> S.genDomain n <*> genNatBV n
                               <*> S.genDomain n <*> genNatBV n
  , genTest "correct_assumeSgt" $
      do SW n <- genWidth
         S.correct_assumeSgt n <$> S.genDomain n <*> genNatBV n
                               <*> S.genDomain n <*> genNatBV n
  , genTest "correct_assumeSge" $
      do SW n <- genWidth
         S.correct_assumeSge n <$> S.genDomain n <*> genNatBV n
                               <*> S.genDomain n <*> genNatBV n
  , genTest "correct_assumeSltPrecise" $
      do SW n <- genWidth
         S.correct_assumeSltPrecise n <$> S.genDomain n <*> genNatBV n
                                      <*> S.genDomain n <*> genNatBV n
  , genTest "correct_assumeSlePrecise" $
      do SW n <- genWidth
         S.correct_assumeSlePrecise n <$> S.genDomain n <*> genNatBV n
                                      <*> S.genDomain n <*> genNatBV n
  , genTest "correct_assumeSgtPrecise" $
      do SW n <- genWidth
         S.correct_assumeSgtPrecise n <$> S.genDomain n <*> genNatBV n
                                      <*> S.genDomain n <*> genNatBV n
  , genTest "correct_assumeSgePrecise" $
      do SW n <- genWidth
         S.correct_assumeSgePrecise n <$> S.genDomain n <*> genNatBV n
                                      <*> S.genDomain n <*> genNatBV n
  , genTest "assumeUltShrinks" $
      do SW n <- genWidth
         S.assumeUltShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeUleShrinks" $
      do SW n <- genWidth
         S.assumeUleShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeUgtShrinks" $
      do SW n <- genWidth
         S.assumeUgtShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeUgeShrinks" $
      do SW n <- genWidth
         S.assumeUgeShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSltShrinks" $
      do SW n <- genWidth
         S.assumeSltShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSleShrinks" $
      do SW n <- genWidth
         S.assumeSleShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSgtShrinks" $
      do SW n <- genWidth
         S.assumeSgtShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSgeShrinks" $
      do SW n <- genWidth
         S.assumeSgeShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSltPreciseShrinks" $
      do SW n <- genWidth
         S.assumeSltPreciseShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSlePreciseShrinks" $
      do SW n <- genWidth
         S.assumeSlePreciseShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSgtPreciseShrinks" $
      do SW n <- genWidth
         S.assumeSgtPreciseShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSgePreciseShrinks" $
      do SW n <- genWidth
         S.assumeSgePreciseShrinks n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSltPreciseIdempotent" $
      do SW n <- genWidth
         S.assumeSltPreciseIdempotent n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSlePreciseIdempotent" $
      do SW n <- genWidth
         S.assumeSlePreciseIdempotent n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSgtPreciseIdempotent" $
      do SW n <- genWidth
         S.assumeSgtPreciseIdempotent n <$> S.genDomain n <*> S.genDomain n
  , genTest "assumeSgePreciseIdempotent" $
      do SW n <- genWidth
         S.assumeSgePreciseIdempotent n <$> S.genDomain n <*> S.genDomain n

  -- Reduced product with bitwise
  , genTest "knownZerosOnesNatDisjoint" $
      do SW n <- genWidth
         S.knownZerosOnesNatDisjoint <$> B.genDomain n
  , genTest "knownZerosOnesNatMember" $
      do SW n <- genWidth
         S.knownZerosOnesNatMember <$> B.genDomain n <*> genNatBV n
  , genTest "liftForcedBitsShrinks" $
      do SW n <- genWidth
         S.liftForcedBitsShrinks n <$> S.genDomain n <*> B.genDomain n
  , genTest "liftForcedBitsMember" $
      do SW n <- genWidth
         S.liftForcedBitsMember n <$> S.genDomain n <*> B.genDomain n
  , genTest "liftForcedBitsRefinesSpec" $
      do SW n <- genWidth
         S.liftForcedBitsRefinesSpec n <$> S.genDomain n <*> B.genDomain n
  , genTest "arcClipBitwiseShrinks" $
      do SW n <- genWidth
         S.arcClipBitwiseShrinks n <$> S.genDomain n <*> genNatBV n <*> genNatBV n
  , genTest "arcClipBitwiseMember" $
      do SW n <- genWidth
         S.arcClipBitwiseMember n <$> S.genDomain n <*> genNatBV n <*> genNatBV n <*> genNatBV n
  , genTest "correct_refineByBits" $
      do SW n <- genWidth
         S.correct_refineByBits n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "refineByBitsShrinks" $
      do SW n <- genWidth
         S.refineByBitsShrinks n <$> S.genDomain n <*> B.genDomain n
  , genTest "correct_refineByBitsPrecise" $
      do SW n <- genWidth
         S.correct_refineByBitsPrecise n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "refineByBitsPreciseShrinks" $
      do SW n <- genWidth
         S.refineByBitsPreciseShrinks n <$> S.genDomain n <*> B.genDomain n
  , genTest "refineByBitsPreciseDominatesRoundTripNonSelfWrap" $
      do SW n <- genWidth
         S.refineByBitsPreciseDominatesRoundTripNonSelfWrap n <$> S.genDomain n <*> B.genDomain n
  , genTest "correct_refineBitsByStrides" $
      do SW n <- genWidth
         S.correct_refineBitsByStrides n <$> B.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "refineBitsByStridesShrinks" $
      do SW n <- genWidth
         S.refineBitsByStridesShrinks n <$> B.genDomain n <*> S.genDomain n
  , genTest "refineBitsByStridesDominatesMeetToBitwise" $
      do SW n <- genWidth
         S.refineBitsByStridesDominatesMeetToBitwise n <$> B.genDomain n <*> S.genDomain n
  , genTest "correct_reduce" $
      do SW n <- genWidth
         S.correct_reduce n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reduceShrinksStrides" $
      do SW n <- genWidth
         S.reduceShrinksStrides n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reduceShrinksBitwise" $
      do SW n <- genWidth
         S.reduceShrinksBitwise n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reduceConflictMeansEmpty" $
      do SW n <- genWidth
         S.reduceConflictMeansEmpty n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "correct_reducePrecise" $
      do SW n <- genWidth
         S.correct_reducePrecise n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reducePreciseShrinksStrides" $
      do SW n <- genWidth
         S.reducePreciseShrinksStrides n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reducePreciseShrinksBitwise" $
      do SW n <- genWidth
         S.reducePreciseShrinksBitwise n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reducePreciseConflictMeansEmpty" $
      do SW n <- genWidth
         S.reducePreciseConflictMeansEmpty n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reducePreciseDominatesReduceStrides" $
      do SW n <- genWidth
         S.reducePreciseDominatesReduceStrides n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reducePreciseDominatesReduceBitwise" $
      do SW n <- genWidth
         S.reducePreciseDominatesReduceBitwise n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reduceFixpointIdempotentStrides" $
      do SW n <- genWidth
         S.reduceFixpointIdempotentStrides n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reduceFixpointIdempotentBitwise" $
      do SW n <- genWidth
         S.reduceFixpointIdempotentBitwise n <$> S.genDomain n <*> B.genDomain n <*> genNatBV n

  -- @S.andPrecise@ and the bitwise lift are /incomparable/ on the
  -- 'leqExact' order: at @w = 4@, exhaustive enumeration finds witnesses
  -- in both directions.
  , TT.testCase "andPrecise incomparable with bitwise lift" $
      let w4 = knownNat @4
          mk s st nn = S.mk w4 s st nn
          liftBand a b =
            fromJust (S.fromBitwise w4 (B.and (S.toBitwise a) (S.toBitwise b)))
          -- Witness: @S.andPrecise a1 b1@ contains an element the lift does
          -- not. a1 = {5,6}, b1 = {2,8}: the lift's per-bit AND forces bits
          -- 0 and 3 to zero, recovering {0,2,4,6} exactly, while
          -- @andPrecise@ returns the stride-1 arc {0,1,2}, whose element 1
          -- has the forced low bit set.
          a1 = mk 5 1 1
          b1 = mk 2 6 1
          -- Witness: lift contains an element @S.andPrecise a2 b2@ does not.
          -- a2 = b2 = {0,1,2}; concrete AND = {0,1,2}, @andPrecise@
          -- recovers it exactly, while the lift drops the orbit-shortness
          -- info and yields @{0,1,2,3}@.
          a2 = mk 0 1 2
          b2 = mk 0 1 2
      in do
        TT.assertBool "andPrecise a1 b1 not <= lift a1 b1"
          (not (S.leqExact (S.andPrecise w4 a1 b1) (liftBand a1 b1)))
        TT.assertBool "lift a2 b2 not <= andPrecise a2 b2"
          (not (S.leqExact (liftBand a2 b2) (S.andPrecise w4 a2 b2)))

  , Precision.tests
  , Internal.tests
  ]
