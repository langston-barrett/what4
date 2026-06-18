{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SmoothClp (tests) where

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
import qualified What4.Domains.BV.SmoothClp as SC
import           What4.Domains.Verification (Gen, chooseInt, chooseInteger, getSize)
import           VerifyBindings (genTest, genTestFew)


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

-- | A small 'Word', for the smooth-stride basis-mask\/exponent properties.
genWord :: Gen Word
genWord = fromIntegral <$> chooseInt (0, 100000)

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
tests = TT.testGroup "SmoothClp"
  [ genTest "modNegCorrect" $
      SC.modNegCorrect <$> genNat <*> genWidthExp
  , genTest "modSubCorrect" $
      SC.modSubCorrect <$> genNat <*> genNat <*> genWidthExp
  , genTest "firstCosetMemberCorrect" $
      SC.firstCosetMemberCorrect <$> genNat <*> genNat <*> genWidthExp <*> genWidthExp
  , genTest "wrapOffsetCorrect" $
      do SW n <- genWidth
         SC.wrapOffsetCorrect <$> SC.genDomain n <*> genNatBV n
  , genTest "strideGcdDividesStride" $
      do SW n <- genWidth
         SC.strideGcdDividesStride <$> SC.genDomain n
  , genTest "strideGcdIsPow2" $
      do SW n <- genWidth
         SC.strideGcdIsPow2 <$> SC.genDomain n
  , genTest "orbitLenViaToList" $
      do SW n <- genWidthSmall
         SC.orbitLenViaToList <$> SC.genDomain n
  , genTest "divByPow2Correct" $
      SC.divByPow2Correct <$> genNat <*> genWidthExp
  , genTest "invModPow2Correct" $
      SC.invModPow2Correct <$> genOddNat <*> genWidthExp
  , genTest "floorSumCorrect" $
      SC.floorSumCorrect <$> genNat <*> genNat <*> genNat <*> genNat
  , genTest "valueIndexCorrect" $
      do SW n <- genWidth
         SC.valueIndexCorrect <$> SC.genDomain n <*> genNatBV n
  , genTest "valueIndexMaybeCorrect" $
      do SW n <- genWidth
         SC.valueIndexMaybeCorrect <$> SC.genDomain n <*> genNatBV n
  , genTest "valueAtCorrect" $
      do SW n <- genWidth
         SC.valueAtCorrect <$> SC.genDomain n <*> genNatBV n
  , genTest "circLeqAtZero" $
      SC.circLeqAtZero <$> genNat <*> genNat <*> genWidthExp
  , genTest "circLeqAnchorMin" $
      SC.circLeqAnchorMin <$> genNat <*> genNat <*> genWidthExp
  , genTest "circLeqAnchorMax" $
      SC.circLeqAnchorMax <$> genNat <*> genNat <*> genWidthExp
  , genTest "isSelfWrappingViaToList" $
      do SW n <- genWidthSmall
         SC.isSelfWrappingViaToList <$> SC.genDomain n
  , genTest "smoothPartDividesAndSquarefree" $
      SC.smoothPartDividesAndSquarefree <$> genNat
  , genTest "smoothGcdDividesTrueGcd" $
      SC.smoothGcdDividesTrueGcd <$> genNat <*> genNat
  , genTestFew "smoothGcdExactOnSmooth" $
      SC.smoothGcdExactOnSmooth <$> genWord <*> genWord <*> genWord <*> genWord
  , genTestFew "smoothLcmExactOnSmooth" $
      SC.smoothLcmExactOnSmooth <$> genWord <*> genWord <*> genWord <*> genWord
  , genTest "smoothCrtAlignCorrect" $
      SC.smoothCrtAlignCorrect <$> genWord <*> genWord <*> genWord <*> genWord
                               <*> genNat <*> genNat
  , genTest "smoothPartDividesStride" $
      do SW n <- genWidth
         SC.smoothPartDividesStride <$> SC.genDomain n
  , genTest "startMember" $
      do SW n <- genWidth
         SC.startMember <$> SC.genDomain n
  , genTest "endMember" $
      do SW n <- genWidth
         SC.endMember <$> SC.genDomain n
  , genTest "toListMember" $
      do SW n <- genWidthSmall
         SC.toListMember <$> SC.genDomain n
  , genTest "memberToList" $
      do SW n <- genWidthSmall
         SC.memberToList <$> SC.genDomain n <*> genNatBV n
  , genTest "memberArcCorrect" $
      do SW n <- genWidth
         SC.memberArcCorrect <$> SC.genDomain n <*> genNatBV n
  , genTest "containsZeroCorrect" $
      do SW n <- genWidth
         SC.containsZeroCorrect <$> SC.genDomain n
  , genTest "toListNoDuplicates" $
      do SW n <- genWidthSmall
         SC.toListNoDuplicates <$> SC.genDomain n
  , genTest "leqCorrect" $
      do SW n <- genWidthSmall
         SC.leqCorrect <$> SC.genDomain n <*> SC.genDomain n
  , genTest "leqReflexive" $
      do SW n <- genWidth
         SC.leqReflexive <$> SC.genDomain n
  , genTestFew "leqTransitive" $
      do SW n <- genWidth
         SC.leqTransitive <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  , genTestFew "leqRefinesLeqExact" $
      do SW n <- genWidthSmall
         SC.leqRefinesLeqExact <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "leqPreciseCorrect" $
      do SW n <- genWidthSmall
         SC.leqPreciseCorrect <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "leqPreciseReflexive" $
      do SW n <- genWidth
         SC.leqPreciseReflexive <$> SC.genDomain n
  , genTestFew "leqPreciseRefinesLeqExact" $
      do SW n <- genWidthSmall
         SC.leqPreciseRefinesLeqExact <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "leqExactCorrect" $
      do SW n <- genWidthSmall
         SC.leqExactCorrect <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "leqExactComplete" $
      do SW n <- genWidthSmall
         SC.leqExactComplete <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "leqExactReflexive" $
      do SW n <- genWidth
         SC.leqExactReflexive <$> SC.genDomain n
  , genTestFew "leqExactTransitive" $
      do SW n <- genWidth
         SC.leqExactTransitive <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  -- 'genWidthSmall' (not 'genWidth'): the reference checks @all (member b)
  -- (toList a)@, which enumerates the full orbit of @a@ in the @a ⊆ b@ case.
  -- Smoothing saturates non-basis strides to full cosets far more often than
  -- the strides domain, so at large widths 'toList' would be intractable.
  , genTestFew "leqExactPartialAgrees" $
      do SW n <- genWidthSmall
         SC.leqExactPartialAgrees <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "leqExactWindowAgrees" $
      do SW n <- genWidthSmall
         SC.leqExactWindowAgrees <$> SC.genDomain n <*> SC.genDomain n
  , genTest "sizeViaToList" $
      do SW n <- genWidthSmall
         SC.sizeViaToList <$> SC.genDomain n
  , genTest "cosetsDisjointCorrect" $
      do SW n <- genWidth
         SC.cosetsDisjointCorrect <$> SC.genDomain n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "eqExactCorrect" $
      do SW n <- genWidthSmall
         SC.eqExactCorrect <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "eqExactReflexive" $
      do SW n <- genWidth
         SC.eqExactReflexive <$> SC.genDomain n
  , genTestFew "eqExactSymmetric" $
      do SW n <- genWidth
         SC.eqExactSymmetric <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "eqExactTransitive" $
      do SW n <- genWidth
         SC.eqExactTransitive <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  , genTest "canonLossless" $
      do SW n <- genWidthSmall
         SC.canonLossless <$> SC.genDomain n
  , genTest "canonProper" $
      do SW n <- genWidth
         SC.canonProper <$> SC.genDomain n
  , genTest "canonUnique" $
      do SW n <- genWidthSmall
         SC.canonUnique <$> SC.genDomain n <*> SC.genDomain n
  , genTest "canonIdempotent" $
      do SW n <- genWidth
         SC.canonIdempotent <$> SC.genDomain n
  , genTest "eqCorrect" $
      do SW n <- genWidthSmall
         SC.eqCorrect <$> SC.genDomain n <*> SC.genDomain n
  , genTest "canonForwardOriented" $
      do SW n <- genWidth
         SC.canonForwardOriented <$> SC.genDomain n
  -- Reference enumerates all (stride, start, n) triples, so cap the width.
  , genTest "canonMatchesSearch" $
      do SW n <- genWidthTiny
         SC.canonMatchesSearch n <$> SC.genDomain n
  , genTest "canonHashRespectsEq" $
      do SW n <- genWidth
         SC.canonHashRespectsEq <$> SC.genDomain n <*> SC.genDomain n
  , genTest "toArithCorrect" $
      do SW n <- genWidth
         SC.toArithCorrect n <$> SC.genDomain n <*> genNatBV n
  , genTest "startEndArcCorrect" $
      do SW n <- genWidth
         SC.startEndArcCorrect n <$> SC.genDomain n <*> genNatBV n
  , genTest "cosetArcCorrect" $
      do SW n <- genWidth
         SC.cosetArcCorrect n <$> SC.genDomain n <*> genNatBV n
  , genTest "fromArithCorrect" $
      do SW n <- genWidth
         SC.fromArithCorrect n <$> A.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "roundtripArith" $
      do SW n <- genWidth
         SC.roundtripArith n <$> A.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "toBitwiseCorrect" $
      do SW n <- genWidth
         SC.toBitwiseCorrect n <$> SC.genDomain n <*> genNatBV n
  , genTest "strideBitwiseCorrect" $
      do SW n <- genWidth
         SC.strideBitwiseCorrect n <$> SC.genDomain n <*> genNatBV n
  , genTest "forcedBitsDisjoint" $
      do SW n <- genWidth
         SC.forcedBitsDisjoint <$> SC.genDomain n
  , genTest "forcedBitsMember" $
      do SW n <- genWidth
         SC.forcedBitsMember <$> SC.genDomain n <*> genNatBV n
  , genTest "nextAgreeingCorrect" $
      do SW n <- genWidth
         SC.nextAgreeingCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n <*> genNatBV n
  , genTest "prevAgreeingCorrect" $
      do SW n <- genWidth
         SC.prevAgreeingCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n <*> genNatBV n
  , genTest "arcExtremesCorrect" $
      do SW n <- genWidth
         SC.arcExtremesCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n
           <*> genNatBV n <*> genNatBV n
  , genTest "fromForcedBitsArcCorrect" $
      do SW n <- genWidth
         SC.fromForcedBitsArcCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n
           <*> genNatBV n <*> genNatBV n
  , genTest "fromForcedCorrect" $
      do SW n <- genWidth
         SC.fromForcedCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n
  , genTest "fromForcedBitsCorrect" $
      do SW n <- genWidth
         SC.fromForcedBitsCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n
           <*> genNatBV n <*> genNatBV n
  , genTest "fromForcedBitsSignedCorrect" $
      do SW n <- genWidth
         SC.fromForcedBitsSignedCorrect n
           <$> genNatBV n <*> genNatBV n <*> genNatBV n
           <*> genNatBV n <*> genNatBV n
  , genTest "fromBitwiseCorrect" $
      do SW n <- genWidth
         SC.fromBitwiseCorrect n <$> B.genDomain n <*> chooseInteger (0, maxUnsigned n)
  , genTest "fromAscEltListMember" $
      do SW n <- genWidth
         SC.fromAscEltListMember n <$> genAscNatList n
  , genTestFew "fromAscEltListToListExactNonWrapping" $
      do SW n <- genWidthSmall
         SC.fromAscEltListToListExactNonWrapping n <$> SC.genDomain n
  , genTest "mkSmoothingSound" $
      do SW n <- genWidth
         SC.mkSmoothingSound n <$> genNat <*> genNat <*> genNat <*> genNat
  , genTest "coarsenToSmoothSound" $
      do SW n <- genWidth
         SC.coarsenToSmoothSound n <$> SC.genDomain n <*> genNat

  -- Arithmetic
  , genTest "correct_neg" $
      do SW n <- genWidth
         (\c x -> SC.correct_neg n c x) <$> SC.genDomain n <*> genNatBV n
  , genTest "reverseDSameSet" $
      do SW n <- genWidthSmall
         SC.reverseDSameSet n <$> SC.genDomain n
  , genTest "psplitProper" $
      do SW n <- genWidth
         SC.psplitProper n <$> SC.genDomain n
  , genTest "psplitCovers" $
      do SW n <- genWidthSmall
         SC.psplitCovers n <$> SC.genDomain n
  , genTest "psplitPartitions" $
      do SW n <- genWidthSmall
         SC.psplitPartitions n <$> SC.genDomain n
  , genTest "psplitOp2Sound" $
      do SW n <- genWidth
         SC.psplitOp2Sound n <$> SC.genDomain n <*> genNatBV n
                            <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_add" $
      do SW n <- genWidth
         SC.correct_add n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "addRobustDominatesRaw" $
      do SW n <- genWidth
         SC.addRobustDominatesRaw n <$> SC.genDomain n <*> SC.genDomain n
  -- addSubSizeCorrect, addRobustClosedFormAgrees removed (see SmoothClp.hs)
  , genTest "correct_sub" $
      do SW n <- genWidth
         SC.correct_sub n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "subRobustDominatesRaw" $
      do SW n <- genWidth
         SC.subRobustDominatesRaw n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "correct_scale" $
      do SW n <- genWidth
         SC.correct_scale n <$> chooseInteger (0, maxUnsigned n)
                           <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_mul" $
      do SW n <- genWidth
         SC.correct_mul n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "mulRobustDominatesRaw" $
      do SW n <- genWidth
         SC.mulRobustDominatesRaw n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "correct_mulCorners" $
      do SW n <- genWidth
         SC.correct_mulCorners n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_mulNoStraddleU" $
      do SW n <- genWidth
         SC.correct_mulNoStraddleU n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_mulNoStraddleS" $
      do SW n <- genWidth
         SC.correct_mulNoStraddleS n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_scaleSingleton" $
      do SW n <- genWidth
         SC.correct_scaleSingleton n <$> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "zboundsArcSameModular" $
      do SW n <- genWidth
         SC.zboundsArcSameModular <$> SC.genDomain n
  , genTest "zboundsArcMinMidpoint" $
      do SW n <- genWidth
         SC.zboundsArcMinMidpoint <$> SC.genDomain n
  , genTest "cornerArcEncloses" $
      do SW n <- genWidth
         SC.cornerArcEncloses <$> SC.genDomain n <*> SC.genDomain n <*> genNatBV n <*> genNatBV n
  , genTest "cornerProductStrideDivides" $
      do SW n <- genWidth
         SC.cornerProductStrideDivides <$> SC.genDomain n <*> SC.genDomain n <*> genNatBV n <*> genNatBV n
  , genTest "clpStepBoundSound" $
      do SW n <- genWidth
         SC.clpStepBoundSound <$> SC.genDomain n <*> SC.genDomain n <*> genNatBV n <*> genNatBV n
  , genTest "arcStepBoundSound" $
      do SW n <- genWidth
         SC.arcStepBoundSound <$> SC.genDomain n <*> SC.genDomain n <*> genNatBV n <*> genNatBV n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         SC.correct_udiv n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_urem" $
      do SW n <- genWidth
         SC.correct_urem n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         SC.correct_sdiv n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_srem" $
      do SW n <- genWidth
         SC.correct_srem n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n

  -- Exactness
  , genTestFew "addExact" $
      do SW n <- genWidthSmall
         SC.addExact n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "subExact" $
      do SW n <- genWidthSmall
         SC.subExact n <$> SC.genDomain n <*> SC.genDomain n
  -- mulConstExact removed under smoothing (see SmoothClp.hs)
  , genTestFew "udivConstExact" $
      do SW n <- genWidthSmall
         SC.udivConstExact n <$> genNatBV n <*> SC.genDomain n
  , genTestFew "uremConstExact" $
      do SW n <- genWidthSmall
         SC.uremConstExact n <$> genNatBV n <*> SC.genDomain n
  , genTestFew "ultExactTrueSeparated" $
      do SW n <- genWidthSmall
         SC.ultExactTrueSeparated n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "ultExactFalseSeparated" $
      do SW n <- genWidthSmall
         SC.ultExactFalseSeparated n <$> SC.genDomain n <*> SC.genDomain n

  , genTest "correct_udivSmtlib" $
      do SW n <- genWidth
         SC.correct_udivSmtlib n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_uremSmtlib" $
      do SW n <- genWidth
         SC.correct_uremSmtlib n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_sdivSmtlib" $
      do SW n <- genWidth
         SC.correct_sdivSmtlib n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_sremSmtlib" $
      do SW n <- genWidth
         SC.correct_sremSmtlib n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n

  -- Arithmetic (LLVM overflow flags) - soundness
  , genTest "correct_addNuw" $
      do SW n <- genWidth
         SC.correct_addNuw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_addNsw" $
      do SW n <- genWidth
         SC.correct_addNsw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_addNswNuw" $
      do SW n <- genWidth
         SC.correct_addNswNuw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_subNuw" $
      do SW n <- genWidth
         SC.correct_subNuw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_subNsw" $
      do SW n <- genWidth
         SC.correct_subNsw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_subNswNuw" $
      do SW n <- genWidth
         SC.correct_subNswNuw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_mulNuw" $
      do SW n <- genWidth
         SC.correct_mulNuw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_mulNsw" $
      do SW n <- genWidth
         SC.correct_mulNsw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_mulNswNuw" $
      do SW n <- genWidth
         SC.correct_mulNswNuw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_shlNuw" $
      do SW n <- genWidth
         SC.correct_shlNuw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_shlNsw" $
      do SW n <- genWidth
         SC.correct_shlNsw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_shlNswNuw" $
      do SW n <- genWidth
         SC.correct_shlNswNuw n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_udivExact" $
      do SW n <- genWidth
         SC.correct_udivExact n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_sdivExact" $
      do SW n <- genWidth
         SC.correct_sdivExact n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_lshrExact" $
      do SW n <- genWidth
         SC.correct_lshrExact n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_ashrExact" $
      do SW n <- genWidth
         SC.correct_ashrExact n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n

  -- Arithmetic (LLVM overflow flags) - dominance over unflagged op
  , genTest "addNuwDominatesAdd" $
      do SW n <- genWidth
         SC.addNuwDominatesAdd n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "addNswDominatesAdd" $
      do SW n <- genWidth
         SC.addNswDominatesAdd n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "addNswNuwDominatesAdd" $
      do SW n <- genWidth
         SC.addNswNuwDominatesAdd n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "subNuwDominatesSub" $
      do SW n <- genWidth
         SC.subNuwDominatesSub n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "subNswDominatesSub" $
      do SW n <- genWidth
         SC.subNswDominatesSub n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "subNswNuwDominatesSub" $
      do SW n <- genWidth
         SC.subNswNuwDominatesSub n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "mulNuwDominatesMul" $
      do SW n <- genWidth
         SC.mulNuwDominatesMul n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "mulNswDominatesMul" $
      do SW n <- genWidth
         SC.mulNswDominatesMul n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "mulNswNuwDominatesMul" $
      do SW n <- genWidth
         SC.mulNswNuwDominatesMul n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "shlNuwDominatesShl" $
      do SW n <- genWidth
         SC.shlNuwDominatesShl n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "shlNswDominatesShl" $
      do SW n <- genWidth
         SC.shlNswDominatesShl n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "shlNswNuwDominatesShl" $
      do SW n <- genWidth
         SC.shlNswNuwDominatesShl n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "udivExactDominatesUdiv" $
      do SW n <- genWidth
         SC.udivExactDominatesUdiv n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "sdivExactDominatesSdiv" $
      do SW n <- genWidth
         SC.sdivExactDominatesSdiv n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "lshrExactDominatesLshr" $
      do SW n <- genWidth
         SC.lshrExactDominatesLshr n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "ashrExactDominatesAshr" $
      do SW n <- genWidth
         SC.ashrExactDominatesAshr n <$> SC.genDomain n <*> SC.genDomain n

  -- Arithmetic (LLVM overflow flags) - combined nsw+nuw refines each single flag
  , genTest "addNswNuwRefinesNsw" $
      do SW n <- genWidth
         SC.addNswNuwRefinesNsw n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "addNswNuwRefinesNuw" $
      do SW n <- genWidth
         SC.addNswNuwRefinesNuw n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "subNswNuwRefinesNsw" $
      do SW n <- genWidth
         SC.subNswNuwRefinesNsw n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "subNswNuwRefinesNuw" $
      do SW n <- genWidth
         SC.subNswNuwRefinesNuw n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "mulNswNuwRefinesNsw" $
      do SW n <- genWidth
         SC.mulNswNuwRefinesNsw n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "mulNswNuwRefinesNuw" $
      do SW n <- genWidth
         SC.mulNswNuwRefinesNuw n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "shlNswNuwRefinesNsw" $
      do SW n <- genWidth
         SC.shlNswNuwRefinesNsw n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "shlNswNuwRefinesNuw" $
      do SW n <- genWidth
         SC.shlNswNuwRefinesNuw n <$> SC.genDomain n <*> SC.genDomain n

  -- Bitwise
  , genTest "correct_not" $
      do SW n <- genWidth
         (\c x -> SC.correct_not n c x) <$> SC.genDomain n <*> genNatBV n
  , genTest "correct_and" $
      do SW n <- genWidth
         SC.correct_and n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_or" $
      do SW n <- genWidth
         SC.correct_or n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_xor" $
      do SW n <- genWidth
         SC.correct_xor n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_andPrecise" $
      do SW n <- genWidth
         SC.correct_andPrecise n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_orPrecise" $
      do SW n <- genWidth
         SC.correct_orPrecise n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_andSingleton" $
      do SW n <- genWidth
         SC.correct_andSingleton n <$> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "andSingletonLowMaskSound" $
      do SW n <- genWidth
         SC.andSingletonLowMaskSound n <$> chooseInt (0, 128) <*> SC.genDomain n <*> genNatBV n
  , genTest "warrenAndLoCorrect" $
      SC.warrenAndLoCorrect <$> genNat <*> genNat <*> genNat <*> genNat
                           <*> genNat <*> genNat <*> genWidthExp
  , genTest "warrenAndHiCorrect" $
      SC.warrenAndHiCorrect <$> genNat <*> genNat <*> genNat <*> genNat
                           <*> genNat <*> genNat <*> genWidthExp
  , genTest "operandRangeCorrect" $
      do SW n <- genWidth
         SC.operandRangeCorrect <$> SC.genDomain n <*> genNatBV n
  , genTestFew "andPreciseDominatesAndFast" $
      do SW n <- genWidth
         SC.andPreciseDominatesAndFast n <$> SC.genDomain n <*> SC.genDomain n

  -- Concatenation, extension, selection, and truncation
  , genTest "correct_zero_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- SC.genDomain w
                x <- genNatBV w
                pure (SC.correct_zero_ext w c u x)
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- SC.genDomain w
                x <- genNatBV w
                pure (SC.correct_sign_ext w c u x)
  , genTest "correct_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- SC.genDomain m
         x <- genNatBV m
         b <- SC.genDomain n
         y <- genNatBV n
         pure (SC.correct_concat m a x n b y)
  , genTest "correct_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         c <- SC.genDomain w
         x <- genNatBV w
         pure (SC.correct_select i n w c x)

  -- Shifts and rotations
  , genTest "correct_shl" $
      do SW n <- genWidth
         SC.correct_shl n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_lshr" $
      do SW n <- genWidth
         SC.correct_lshr n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_ashr" $
      do SW n <- genWidth
         SC.correct_ashr n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_rol" $
      do SW n <- genWidth
         SC.correct_rol n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_rolPrecise" $
      do SW n <- genWidth
         SC.correct_rolPrecise n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "rolPreciseRawDominatesRolRaw" $
      do SW n <- genWidth
         SC.rolPreciseRawDominatesRolRaw n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "correct_ror" $
      do SW n <- genWidth
         SC.correct_ror n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_rorPrecise" $
      do SW n <- genWidth
         SC.correct_rorPrecise n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "rorPreciseRawDominatesRorRaw" $
      do SW n <- genWidth
         SC.rorPreciseRawDominatesRorRaw n <$> SC.genDomain n <*> SC.genDomain n

  -- Lattice operations
  , genTest "correct_pseudoMeet" $
      do SW n <- genWidth
         SC.correct_pseudoMeet n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_pseudoMeetPrecise" $
      do SW n <- genWidth
         SC.correct_pseudoMeetPrecise n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "pseudoMeetLowerBound" $
      do SW n <- genWidth
         SC.pseudoMeetLowerBound n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "pseudoMeetPreciseLowerBound" $
      do SW n <- genWidth
         SC.pseudoMeetPreciseLowerBound n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "pseudoMeetCommutative" $
      do SW n <- genWidth
         SC.pseudoMeetCommutative n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "pseudoMeetPreciseCommutative" $
      do SW n <- genWidth
         SC.pseudoMeetPreciseCommutative n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "pseudoMeetIdempotent" $
      do SW n <- genWidth
         SC.pseudoMeetIdempotent n <$> SC.genDomain n
  , genTestFew "pseudoMeetPreciseIdempotent" $
      do SW n <- genWidth
         SC.pseudoMeetPreciseIdempotent n <$> SC.genDomain n
  , genTest "nsplitUnion" $
      do SW n <- genWidth
         SC.nsplitUnion n <$> SC.genDomain n <*> genNatBV n
  , genTest "nsplitDisjoint" $
      do SW n <- genWidth
         SC.nsplitDisjoint n <$> SC.genDomain n <*> genNatBV n
  , genTest "ssplitUnion" $
      do SW n <- genWidth
         SC.ssplitUnion n <$> SC.genDomain n <*> genNatBV n
  , genTest "ssplitDisjoint" $
      do SW n <- genWidth
         SC.ssplitDisjoint n <$> SC.genDomain n <*> genNatBV n
  , genTest "correct_pseudoJoin" $
      do SW n <- genWidth
         SC.correct_pseudoJoin n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_pseudoJoinPrecise" $
      do SW n <- genWidth
         SC.correct_pseudoJoinPrecise n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "pseudoJoinUpperBound" $
      do SW n <- genWidth
         SC.pseudoJoinUpperBound n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "pseudoJoinPreciseUpperBound" $
      do SW n <- genWidth
         SC.pseudoJoinPreciseUpperBound n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "pseudoJoinCommutative" $
      do SW n <- genWidth
         SC.pseudoJoinCommutative n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "pseudoJoinPreciseCommutative" $
      do SW n <- genWidth
         SC.pseudoJoinPreciseCommutative n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "pseudoJoinIdempotent" $
      do SW n <- genWidth
         SC.pseudoJoinIdempotent n <$> SC.genDomain n
  , genTestFew "pseudoJoinPreciseIdempotent" $
      do SW n <- genWidth
         SC.pseudoJoinPreciseIdempotent n <$> SC.genDomain n
  , genTestFew "pseudoJoinPreciseRefinesJoin" $
      do SW n <- genWidth
         SC.pseudoJoinPreciseRefinesJoin n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "pseudoJoinMinimalUpperBound" $
      do SW n <- genWidth
         SC.pseudoJoinMinimalUpperBound n <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  , genTestFew "pseudoJoinPreciseMinimalUpperBound" $
      do SW n <- genWidth
         SC.pseudoJoinPreciseMinimalUpperBound n <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  , genTestFew "boundingBoxJoinMinimalUpperBound" $
      do SW n <- genWidth
         SC.boundingBoxJoinMinimalUpperBound n <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  , genTestFew "pseudoMeetMaximalLowerBound" $
      do SW n <- genWidth
         SC.pseudoMeetMaximalLowerBound n <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  , genTestFew "pseudoMeetPreciseMaximalLowerBound" $
      do SW n <- genWidth
         SC.pseudoMeetPreciseMaximalLowerBound n <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  , genTest "lowerBoundMaximalAmongCandidates" $
      do SW n <- genWidth
         SC.lowerBoundMaximalAmongCandidates n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "pseudoMeetTopIdentity" $
      do SW n <- genWidth
         SC.pseudoMeetTopIdentity n <$> SC.genDomain n
  , genTestFew "pseudoMeetPreciseTopIdentity" $
      do SW n <- genWidth
         SC.pseudoMeetPreciseTopIdentity n <$> SC.genDomain n
  , genTest "pseudoJoinTopAnnihilator" $
      do SW n <- genWidth
         SC.pseudoJoinTopAnnihilator n <$> SC.genDomain n
  , genTestFew "pseudoJoinPreciseTopAnnihilator" $
      do SW n <- genWidth
         SC.pseudoJoinPreciseTopAnnihilator n <$> SC.genDomain n
  , genTest "correct_boundingBoxJoin" $
      do SW n <- genWidth
         SC.correct_boundingBoxJoin n <$> SC.genDomain n <*> genNatBV n <*> SC.genDomain n <*> genNatBV n
  , genTest "boundingBoxJoinCommutative" $
      do SW n <- genWidth
         SC.boundingBoxJoinCommutative n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "boundingBoxJoinIdempotent" $
      do SW n <- genWidth
         SC.boundingBoxJoinIdempotent n <$> SC.genDomain n
  , genTest "boundingBoxJoinTopAnnihilator" $
      do SW n <- genWidth
         SC.boundingBoxJoinTopAnnihilator n <$> SC.genDomain n
  , genTest "boundingBoxJoinUpperBound" $
      do SW n <- genWidth
         SC.boundingBoxJoinUpperBound n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "boundingBoxJoinAssociative" $
      do SW n <- genWidth
         SC.boundingBoxJoinAssociative n <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  , genTest "boundingBoxJoinMonotone" $
      do SW n <- genWidth
         SC.boundingBoxJoinMonotone n <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  , genTest "pseudoJoinDominatesBoundingBoxJoin" $
      do SW n <- genWidth
         SC.pseudoJoinDominatesBoundingBoxJoin n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "correct_exactJoin" $
      do SW n <- genWidth
         SC.correct_exactJoin n <$> SC.genDomain n <*> SC.genDomain n <*> genNatBV n
  , genTest "exactJoinCommutative" $
      do SW n <- genWidth
         SC.exactJoinCommutative n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "exactJoinIdempotent" $
      do SW n <- genWidth
         SC.exactJoinIdempotent n <$> SC.genDomain n
  , genTest "exactJoinUpperBound" $
      do SW n <- genWidth
         SC.exactJoinUpperBound n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "exactJoinTopAnnihilator" $
      do SW n <- genWidth
         SC.exactJoinTopAnnihilator n <$> SC.genDomain n
  , genTest "exactJoinAssociative" $
      do SW n <- genWidth
         SC.exactJoinAssociative n <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  , genTest "correct_exactMeet" $
      do SW n <- genWidth
         SC.correct_exactMeet n <$> SC.genDomain n <*> SC.genDomain n <*> genNatBV n
  , genTest "exactMeetCommutative" $
      do SW n <- genWidth
         SC.exactMeetCommutative n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "exactMeetIdempotent" $
      do SW n <- genWidth
         SC.exactMeetIdempotent n <$> SC.genDomain n
  , genTest "exactMeetLowerBound" $
      do SW n <- genWidth
         SC.exactMeetLowerBound n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "exactMeetTopIdentity" $
      do SW n <- genWidth
         SC.exactMeetTopIdentity n <$> SC.genDomain n
  , genTest "exactMeetAssociative" $
      do SW n <- genWidth
         SC.exactMeetAssociative n <$> SC.genDomain n <*> SC.genDomain n <*> SC.genDomain n
  , genTest "lowerBoundDominatedByPseudoMeet" $
      do SW n <- genWidth
         SC.lowerBoundDominatedByPseudoMeet n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "correct_lowerBound" $
      do SW n <- genWidth
         SC.correct_lowerBound n <$> SC.genDomain n <*> SC.genDomain n <*> genNatBV n
  , genTestFew "lowerBoundLeqExactBoth" $
      do SW n <- genWidth
         SC.lowerBoundLeqExactBoth n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "lowerBoundCommutative" $
      do SW n <- genWidth
         SC.lowerBoundCommutative n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "lowerBoundIdempotent" $
      do SW n <- genWidth
         SC.lowerBoundIdempotent n <$> SC.genDomain n
  , genTest "lowerBoundTopIdentity" $
      do SW n <- genWidth
         SC.lowerBoundTopIdentity n <$> SC.genDomain n
  , genTest "lowerBoundIsLargestLowerBound" $
      do SW n <- genWidth
         SC.lowerBoundIsLargestLowerBound n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "correct_lowerBounds" $
      do SW n <- genWidth
         SC.correct_lowerBounds n <$> SC.genDomain n <*> SC.genDomain n <*> genNatBV n
  , genTest "lowerBoundsAllSubsets" $
      do SW n <- genWidth
         SC.lowerBoundsAllSubsets n <$> SC.genDomain n <*> SC.genDomain n
  -- Uses 'toList' to compare element sets, so capped at small widths.
  , genTest "correct_compactify" $
      do SW n <- genWidthSmall
         k <- chooseInt (0, 4)
         cs <- mapM (const (SC.genDomain n)) [1 .. k]
         pure (SC.correct_compactify n cs)
  , genTest "trimSelfWrapNotSelfWrapping" $
      do SW n <- genWidth
         SC.trimSelfWrapNotSelfWrapping n <$> SC.genDomain n
  , genTest "trimSelfWrapSubset" $
      do SW n <- genWidth
         SC.trimSelfWrapSubset n <$> SC.genDomain n
  , genTest "trimSelfWrapIdentity" $
      do SW n <- genWidth
         SC.trimSelfWrapIdentity n <$> SC.genDomain n
  , genTest "trimSelfWrapIdempotent" $
      do SW n <- genWidth
         SC.trimSelfWrapIdempotent n <$> SC.genDomain n

  -- Branch-condition assumptions
  , genTest "correct_assumeUlt" $
      do SW n <- genWidth
         SC.correct_assumeUlt n <$> SC.genDomain n <*> genNatBV n
                               <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_assumeUle" $
      do SW n <- genWidth
         SC.correct_assumeUle n <$> SC.genDomain n <*> genNatBV n
                               <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_assumeUgt" $
      do SW n <- genWidth
         SC.correct_assumeUgt n <$> SC.genDomain n <*> genNatBV n
                               <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_assumeUge" $
      do SW n <- genWidth
         SC.correct_assumeUge n <$> SC.genDomain n <*> genNatBV n
                               <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_assumeSlt" $
      do SW n <- genWidth
         SC.correct_assumeSlt n <$> SC.genDomain n <*> genNatBV n
                               <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_assumeSle" $
      do SW n <- genWidth
         SC.correct_assumeSle n <$> SC.genDomain n <*> genNatBV n
                               <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_assumeSgt" $
      do SW n <- genWidth
         SC.correct_assumeSgt n <$> SC.genDomain n <*> genNatBV n
                               <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_assumeSge" $
      do SW n <- genWidth
         SC.correct_assumeSge n <$> SC.genDomain n <*> genNatBV n
                               <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_assumeSltPrecise" $
      do SW n <- genWidth
         SC.correct_assumeSltPrecise n <$> SC.genDomain n <*> genNatBV n
                                      <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_assumeSlePrecise" $
      do SW n <- genWidth
         SC.correct_assumeSlePrecise n <$> SC.genDomain n <*> genNatBV n
                                      <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_assumeSgtPrecise" $
      do SW n <- genWidth
         SC.correct_assumeSgtPrecise n <$> SC.genDomain n <*> genNatBV n
                                      <*> SC.genDomain n <*> genNatBV n
  , genTestFew "correct_assumeSgePrecise" $
      do SW n <- genWidth
         SC.correct_assumeSgePrecise n <$> SC.genDomain n <*> genNatBV n
                                      <*> SC.genDomain n <*> genNatBV n
  , genTest "correct_assumeNe" $
      do SW n <- genWidth
         SC.correct_assumeNe n <$> SC.genDomain n <*> genNatBV n
                              <*> SC.genDomain n <*> genNatBV n
  , genTest "assumeUltShrinks" $
      do SW n <- genWidth
         SC.assumeUltShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "assumeUleShrinks" $
      do SW n <- genWidth
         SC.assumeUleShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "assumeUgtShrinks" $
      do SW n <- genWidth
         SC.assumeUgtShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "assumeUgeShrinks" $
      do SW n <- genWidth
         SC.assumeUgeShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "assumeSltShrinks" $
      do SW n <- genWidth
         SC.assumeSltShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "assumeSleShrinks" $
      do SW n <- genWidth
         SC.assumeSleShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "assumeSgtShrinks" $
      do SW n <- genWidth
         SC.assumeSgtShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "assumeSgeShrinks" $
      do SW n <- genWidth
         SC.assumeSgeShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "assumeSltPreciseShrinks" $
      do SW n <- genWidth
         SC.assumeSltPreciseShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "assumeSlePreciseShrinks" $
      do SW n <- genWidth
         SC.assumeSlePreciseShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "assumeSgtPreciseShrinks" $
      do SW n <- genWidth
         SC.assumeSgtPreciseShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "assumeSgePreciseShrinks" $
      do SW n <- genWidth
         SC.assumeSgePreciseShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTest "assumeNeShrinks" $
      do SW n <- genWidth
         SC.assumeNeShrinks n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "assumeSltPreciseIdempotent" $
      do SW n <- genWidth
         SC.assumeSltPreciseIdempotent n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "assumeSlePreciseIdempotent" $
      do SW n <- genWidth
         SC.assumeSlePreciseIdempotent n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "assumeSgtPreciseIdempotent" $
      do SW n <- genWidth
         SC.assumeSgtPreciseIdempotent n <$> SC.genDomain n <*> SC.genDomain n
  , genTestFew "assumeSgePreciseIdempotent" $
      do SW n <- genWidth
         SC.assumeSgePreciseIdempotent n <$> SC.genDomain n <*> SC.genDomain n

  -- Reduced product with bitwise
  , genTest "knownZerosOnesNatDisjoint" $
      do SW n <- genWidth
         SC.knownZerosOnesNatDisjoint <$> B.genDomain n
  , genTest "knownZerosOnesNatMember" $
      do SW n <- genWidth
         SC.knownZerosOnesNatMember <$> B.genDomain n <*> genNatBV n
  , genTest "liftForcedBitsShrinks" $
      do SW n <- genWidth
         SC.liftForcedBitsShrinks n <$> SC.genDomain n <*> B.genDomain n
  , genTest "liftForcedBitsMember" $
      do SW n <- genWidth
         SC.liftForcedBitsMember n <$> SC.genDomain n <*> B.genDomain n
  -- liftForcedBitsRefinesSpec disabled under smoothing (see SmoothClp.hs)
  , genTest "arcClipBitwiseShrinks" $
      do SW n <- genWidth
         SC.arcClipBitwiseShrinks n <$> SC.genDomain n <*> genNatBV n <*> genNatBV n
  , genTest "arcClipBitwiseMember" $
      do SW n <- genWidth
         SC.arcClipBitwiseMember n <$> SC.genDomain n <*> genNatBV n <*> genNatBV n <*> genNatBV n
  , genTest "correct_refineByBits" $
      do SW n <- genWidth
         SC.correct_refineByBits n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "refineByBitsShrinks" $
      do SW n <- genWidth
         SC.refineByBitsShrinks n <$> SC.genDomain n <*> B.genDomain n
  , genTestFew "correct_refineByBitsPrecise" $
      do SW n <- genWidth
         SC.correct_refineByBitsPrecise n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTestFew "refineByBitsPreciseShrinks" $
      do SW n <- genWidth
         SC.refineByBitsPreciseShrinks n <$> SC.genDomain n <*> B.genDomain n
  -- refineByBitsPreciseDominatesRoundTripNonSelfWrap removed under smoothing (see SmoothClp.hs)
  , genTest "correct_refineBitsByStrides" $
      do SW n <- genWidth
         SC.correct_refineBitsByStrides n <$> B.genDomain n <*> SC.genDomain n <*> genNatBV n
  , genTest "refineBitsByStridesShrinks" $
      do SW n <- genWidth
         SC.refineBitsByStridesShrinks n <$> B.genDomain n <*> SC.genDomain n
  , genTest "refineBitsByStridesDominatesMeetToBitwise" $
      do SW n <- genWidth
         SC.refineBitsByStridesDominatesMeetToBitwise n <$> B.genDomain n <*> SC.genDomain n
  , genTest "correct_reduce" $
      do SW n <- genWidth
         SC.correct_reduce n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "correct_reduceProject" $
      do SW n <- genWidth
         SC.correct_reduceProject n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reduceShrinksStrides" $
      do SW n <- genWidth
         SC.reduceShrinksStrides n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reduceShrinksBitwise" $
      do SW n <- genWidth
         SC.reduceShrinksBitwise n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reduceConflictMeansEmpty" $
      do SW n <- genWidth
         SC.reduceConflictMeansEmpty n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTestFew "correct_reducePrecise" $
      do SW n <- genWidth
         SC.correct_reducePrecise n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTestFew "reducePreciseShrinksStrides" $
      do SW n <- genWidth
         SC.reducePreciseShrinksStrides n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTestFew "reducePreciseShrinksBitwise" $
      do SW n <- genWidth
         SC.reducePreciseShrinksBitwise n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTestFew "reducePreciseConflictMeansEmpty" $
      do SW n <- genWidth
         SC.reducePreciseConflictMeansEmpty n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTestFew "reducePreciseDominatesReduceStrides" $
      do SW n <- genWidth
         SC.reducePreciseDominatesReduceStrides n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTestFew "reducePreciseDominatesReduceBitwise" $
      do SW n <- genWidth
         SC.reducePreciseDominatesReduceBitwise n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reduceFixpointIdempotentStrides" $
      do SW n <- genWidth
         SC.reduceFixpointIdempotentStrides n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n
  , genTest "reduceFixpointIdempotentBitwise" $
      do SW n <- genWidth
         SC.reduceFixpointIdempotentBitwise n <$> SC.genDomain n <*> B.genDomain n <*> genNatBV n

  -- @SC.andPrecise@ and the bitwise lift are /incomparable/ on the
  -- 'leqExact' order: at @w = 4@, exhaustive enumeration finds witnesses
  -- in both directions.
  , TT.testCase "andPrecise incomparable with bitwise lift" $
      let w4 = knownNat @4
          mk s st nn = SC.mk w4 s st nn
          liftBand a b =
            fromJust (SC.fromBitwise w4 (B.and (SC.toBitwise a) (SC.toBitwise b)))
          -- Witness: @SC.andPrecise a1 b1@ contains an element the lift does
          -- not. a1 = {5,6}, b1 = {2,8}: the lift's per-bit AND forces bits
          -- 0 and 3 to zero, recovering {0,2,4,6} exactly, while
          -- @andPrecise@ returns the stride-1 arc {0,1,2}, whose element 1
          -- has the forced low bit set.
          a1 = mk 5 1 1
          b1 = mk 2 6 1
          -- Witness: lift contains an element @SC.andPrecise a2 b2@ does not.
          -- a2 = b2 = {0,1,2}; concrete AND = {0,1,2}, @andPrecise@
          -- recovers it exactly, while the lift drops the orbit-shortness
          -- info and yields @{0,1,2,3}@.
          a2 = mk 0 1 2
          b2 = mk 0 1 2
      in do
        TT.assertBool "andPrecise a1 b1 not <= lift a1 b1"
          (not (SC.leqExact (SC.andPrecise w4 a1 b1) (liftBand a1 b1)))
        TT.assertBool "lift a2 b2 not <= andPrecise a2 b2"
          (not (SC.leqExact (liftBand a2 b2) (SC.andPrecise w4 a2 b2)))

  ]
