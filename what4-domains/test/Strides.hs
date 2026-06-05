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
  , genTest "correct_eq" $
      do SW n <- genWidth
         S.correct_eq n <$>
           ((,) <$> S.genDomain n <*> genNatBV n) <*>
           ((,) <$> S.genDomain n <*> genNatBV n)
  , genTest "cosetsDisjointCorrect" $
      do SW n <- genWidth
         S.cosetsDisjointCorrect <$> S.genDomain n <*> S.genDomain n <*> genNatBV n
  , genTest "eqExactCorrect" $
      do SW n <- genWidthSmall
         S.eqExactCorrect <$> S.genDomain n <*> S.genDomain n
  , genTest "eqReflexive" $
      do SW n <- genWidth
         S.eqReflexive <$> S.genDomain n
  , genTest "eqSymmetric" $
      do SW n <- genWidth
         S.eqSymmetric <$> S.genDomain n <*> S.genDomain n
  , genTest "eqTransitive" $
      do SW n <- genWidth
         S.eqTransitive <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "eqExactReflexive" $
      do SW n <- genWidth
         S.eqExactReflexive <$> S.genDomain n
  , genTest "eqExactSymmetric" $
      do SW n <- genWidth
         S.eqExactSymmetric <$> S.genDomain n <*> S.genDomain n
  , genTest "eqExactTransitive" $
      do SW n <- genWidth
         S.eqExactTransitive <$> S.genDomain n <*> S.genDomain n <*> S.genDomain n
  , genTest "eqRefinesEqExact" $
      do SW n <- genWidthSmall
         S.eqRefinesEqExact <$> S.genDomain n <*> S.genDomain n
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
  , genTest "correct_add" $
      do SW n <- genWidth
         S.correct_add n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_sub" $
      do SW n <- genWidth
         S.correct_sub n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
  , genTest "correct_scale" $
      do SW n <- genWidth
         S.correct_scale n <$> chooseInteger (0, maxUnsigned n)
                           <*> S.genDomain n <*> genNatBV n
  , genTest "correct_mul" $
      do SW n <- genWidth
         S.correct_mul n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n
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
  , genTest "warrenAndLoCorrect" $
      S.warrenAndLoCorrect <$> genNat <*> genNat <*> genNat <*> genNat
                           <*> genNat <*> genNat <*> genWidthExp
  , genTest "warrenAndHiCorrect" $
      S.warrenAndHiCorrect <$> genNat <*> genNat <*> genNat <*> genNat
                           <*> genNat <*> genNat <*> genWidthExp
  , genTest "operandRangeCorrect" $
      do SW n <- genWidth
         S.operandRangeCorrect <$> S.genDomain n <*> genNatBV n
  , genTest "andPreciseDominatesAnd" $
      do SW n <- genWidth
         S.andPreciseDominatesAnd n <$> S.genDomain n <*> S.genDomain n

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
  , genTest "correct_ror" $
      do SW n <- genWidth
         S.correct_ror n <$> S.genDomain n <*> genNatBV n <*> S.genDomain n <*> genNatBV n

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
  -- @S.andPrecise@ and the bitwise lift are /incomparable/ on the
  -- 'leqExact' order: at @w = 4@, Z3 refutes both directions of dominance.
  -- These manual counter-examples were extracted from those refutations.
  , TT.testCase "andPrecise incomparable with bitwise lift" $
      let w4 = knownNat @4
          mk s st nn = S.mk w4 s st nn
          liftBand a b =
            fromJust (S.fromBitwise w4 (B.and (S.toBitwise a) (S.toBitwise b)))
          -- Witness: @S.andPrecise a1 b1@ contains an element the lift does not.
          a1 = mk 1 12 2
          b1 = mk 1 1  0
          -- Witness: lift contains an element @S.andPrecise a2 b2@ does not.
          a2 = mk 2 4  2
          b2 = mk 12 10 6
      in do
        TT.assertBool "andPrecise a1 b1 not <= lift a1 b1"
          (not (S.leqExact (S.andPrecise w4 a1 b1) (liftBand a1 b1)))
        TT.assertBool "lift a2 b2 not <= andPrecise a2 b2"
          (not (S.leqExact (liftBand a2 b2) (S.andPrecise w4 a2 b2)))

  , Precision.tests
  , Internal.tests
  ]
