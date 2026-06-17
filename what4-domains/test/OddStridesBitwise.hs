{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module OddStridesBitwise (tests) where

import qualified Test.Tasty as TT

import qualified Data.List as List
import           Data.Parameterized.NatRepr
                   ( NatRepr, addNat, addIsLeq, isPosNat, knownNat
                   , someNat, testLeq, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import qualified What4.Domains.BV.OddStridesBitwise as OSB
import           What4.Domains.Verification (Gen, chooseInt, chooseInteger, getSize)
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

genWidthSmall :: Gen SomeWidth
genWidthSmall =
  do x <- chooseInt (1, 8)
     case someNat (fromIntegral x :: Natural) of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidthSmall"

genNatBV :: NatRepr w -> Gen Natural
genNatBV w = fromInteger <$> chooseInteger (0, maxUnsigned w)

genAscNatList :: NatRepr w -> Gen [Natural]
genAscNatList w =
  do sz <- getSize
     k <- chooseInt (0, min (sz + 1) 64)
     ys <- mapM (const (genNatBV w)) [1 .. k]
     pure (List.sort (List.nub ys))

tests :: TT.TestTree
tests = TT.testGroup "OddStridesBitwise"
  [ -- ** Construction
    genTest "fromAscEltListMember" $
      do SW n <- genWidth
         OSB.fromAscEltListMember n <$> genAscNatList n
  -- ** Canonicalization
  , genTest "canonLossless" $
      do SW n <- genWidth
         OSB.canonLossless n <$> OSB.genDomain n <*> genNatBV n
  , genTest "canonProper" $
      do SW n <- genWidth
         OSB.canonProper n <$> OSB.genDomain n
  , genTest "canonIdempotent" $
      do SW n <- genWidth
         OSB.canonIdempotent n <$> OSB.genDomain n <*> genNatBV n
  -- ** Conversion
  , genTest "toArithCorrect" $
      do SW n <- genWidth
         OSB.toArithCorrect n <$> OSB.genDomain n <*> genNatBV n
  , genTest "fromArithCorrect" $
      do SW n <- genWidth
         OSB.fromArithCorrect n <$> A.genDomain n <*> genNatBV n
  , genTest "roundtripArith" $
      do SW n <- genWidthSmall
         OSB.roundtripArith n <$> OSB.genDomain n
  , genTest "toBitwiseCorrect" $
      do SW n <- genWidth
         OSB.toBitwiseCorrect n <$> OSB.genDomain n <*> genNatBV n
  , genTest "forcedBitsMember" $
      do SW n <- genWidth
         OSB.forcedBitsMember n <$> OSB.genDomain n <*> genNatBV n
  , genTest "fromBitwiseCorrect" $
      do SW n <- genWidth
         OSB.fromBitwiseCorrect n <$> B.genDomain n <*> genNatBV n
  -- ** Queries
  , genTest "toListMember" $
      do SW n <- genWidthSmall
         OSB.toListMember n <$> OSB.genDomain n
  , genTest "memberToList" $
      do SW n <- genWidthSmall
         OSB.memberToList n <$> OSB.genDomain n <*> genNatBV n
  , genTest "toListNoDuplicates" $
      do SW n <- genWidthSmall
         OSB.toListNoDuplicates n <$> OSB.genDomain n
  , genTest "leqCorrect" $
      do SW n <- genWidthSmall
         OSB.leqCorrect n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "leqReflexive" $
      do SW n <- genWidth
         OSB.leqReflexive n <$> OSB.genDomain n
  , genTest "leqTransitive" $
      do SW n <- genWidth
         OSB.leqTransitive n <$> OSB.genDomain n <*> OSB.genDomain n <*> OSB.genDomain n
  , genTest "leqPreciseCorrect" $
      do SW n <- genWidthSmall
         OSB.leqPreciseCorrect n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "leqPreciseReflexive" $
      do SW n <- genWidth
         OSB.leqPreciseReflexive n <$> OSB.genDomain n
  , genTest "sizeViaToList" $
      do SW n <- genWidthSmall
         OSB.sizeViaToList n <$> OSB.genDomain n
  , genTest "sizeAtMostComponents" $
      do SW n <- genWidth
         OSB.sizeAtMostComponents n <$> OSB.genDomain n
  , genTest "sizeExactCorrect" $
      do SW n <- genWidthSmall
         OSB.sizeExactCorrect n <$> OSB.genDomain n
  , genTest "windowMarginalCount" $
      do SW n <- genWidthSmall
         OSB.windowMarginalCount n <$> OSB.genDomain n
  , genTest "uniformWindowBalanced" $
      do SW n <- genWidthSmall
         OSB.uniformWindowBalanced n <$> OSB.genDomain n
  , genTest "pinsConflictEmpty" $
      do SW n <- genWidthSmall
         OSB.pinsConflictEmpty n <$> OSB.genDomain n <*> OSB.genDomain n
  -- ** Arithmetic
  , genTest "correct_neg" $
      do SW n <- genWidth
         OSB.correct_neg n <$> OSB.genDomain n <*> genNatBV n
  , genTest "correct_add" $
      do SW n <- genWidth
         OSB.correct_add n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_sub" $
      do SW n <- genWidth
         OSB.correct_sub n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_scale" $
      do SW n <- genWidth
         OSB.correct_scale n <$> chooseInteger (-100, 100) <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_mul" $
      do SW n <- genWidth
         OSB.correct_mul n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_mulPrecise" $
      do SW n <- genWidth
         OSB.correct_mulPrecise n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         OSB.correct_udiv n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_udivPrecise" $
      do SW n <- genWidth
         OSB.correct_udivPrecise n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_urem" $
      do SW n <- genWidth
         OSB.correct_urem n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_uremPrecise" $
      do SW n <- genWidth
         OSB.correct_uremPrecise n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         OSB.correct_sdiv n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_srem" $
      do SW n <- genWidth
         OSB.correct_srem n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "addExact" $
      do SW n <- genWidth
         OSB.addExact n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "subExact" $
      do SW n <- genWidth
         OSB.subExact n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "mulConstExact" $
      do SW n <- genWidth
         OSB.mulConstExact n <$> chooseInteger (-100, 100) <*> OSB.genDomain n
  , genTest "udivConstExact" $
      do SW n <- genWidth
         OSB.udivConstExact n <$> OSB.genDomain n <*> genNatBV n
  , genTest "uremConstExact" $
      do SW n <- genWidth
         OSB.uremConstExact n <$> OSB.genDomain n <*> genNatBV n
  , genTest "ultExactTrueSeparated" $
      do SW n <- genWidth
         OSB.ultExactTrueSeparated n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "ultExactFalseSeparated" $
      do SW n <- genWidth
         OSB.ultExactFalseSeparated n <$> OSB.genDomain n <*> OSB.genDomain n
  -- *** Power-of-2 fast paths
  , genTest "correct_scalePow2" $
      do SW n <- genWidth
         k <- choosePow2Exp n
         OSB.correct_scalePow2 n k <$> OSB.genDomain n <*> genNatBV n
  , genTest "correct_mulPow2" $
      do SW n <- genWidth
         OSB.correct_mulPow2 n <$> OSB.genDomain n <*> genNatBV n <*> genPow2Singleton n
  , genTest "correct_udivPow2" $
      do SW n <- genWidth
         OSB.correct_udivPow2 n <$> OSB.genDomain n <*> genNatBV n <*> genPow2Singleton n
  , genTest "correct_udivPrecisePow2" $
      do SW n <- genWidth
         OSB.correct_udivPrecisePow2 n <$> OSB.genDomain n <*> genNatBV n <*> genPow2Singleton n
  , genTest "correct_uremPow2" $
      do SW n <- genWidth
         OSB.correct_uremPow2 n <$> OSB.genDomain n <*> genNatBV n <*> genPow2Singleton n
  , genTest "correct_uremPrecisePow2" $
      do SW n <- genWidth
         OSB.correct_uremPrecisePow2 n <$> OSB.genDomain n <*> genNatBV n <*> genPow2Singleton n
  -- *** Arithmetic (SMT-LIB div-by-zero semantics)
  , genTest "correct_udivSmtlib" $
      do SW n <- genWidth
         OSB.correct_udivSmtlib n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_uremSmtlib" $
      do SW n <- genWidth
         OSB.correct_uremSmtlib n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_sdivSmtlib" $
      do SW n <- genWidth
         OSB.correct_sdivSmtlib n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_sremSmtlib" $
      do SW n <- genWidth
         OSB.correct_sremSmtlib n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  -- ** Arithmetic (LLVM overflow flags)
  , genTest "correct_addNuw" $
      do SW n <- genWidth
         OSB.correct_addNuw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_addNsw" $
      do SW n <- genWidth
         OSB.correct_addNsw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_addNswNuw" $
      do SW n <- genWidth
         OSB.correct_addNswNuw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_subNuw" $
      do SW n <- genWidth
         OSB.correct_subNuw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_subNsw" $
      do SW n <- genWidth
         OSB.correct_subNsw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_subNswNuw" $
      do SW n <- genWidth
         OSB.correct_subNswNuw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_mulNuw" $
      do SW n <- genWidth
         OSB.correct_mulNuw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_mulNsw" $
      do SW n <- genWidth
         OSB.correct_mulNsw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_mulNswNuw" $
      do SW n <- genWidth
         OSB.correct_mulNswNuw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_shlNuw" $
      do SW n <- genWidth
         OSB.correct_shlNuw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_shlNsw" $
      do SW n <- genWidth
         OSB.correct_shlNsw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_shlNswNuw" $
      do SW n <- genWidth
         OSB.correct_shlNswNuw n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_udivExact" $
      do SW n <- genWidth
         OSB.correct_udivExact n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_sdivExact" $
      do SW n <- genWidth
         OSB.correct_sdivExact n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_lshrExact" $
      do SW n <- genWidth
         OSB.correct_lshrExact n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_ashrExact" $
      do SW n <- genWidth
         OSB.correct_ashrExact n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  -- ** Bitwise operations
  , genTest "correct_not" $
      do SW n <- genWidth
         OSB.correct_not n <$> OSB.genDomain n <*> genNatBV n
  , genTest "correct_and" $
      do SW n <- genWidth
         OSB.correct_and n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_or" $
      do SW n <- genWidth
         OSB.correct_or n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_xor" $
      do SW n <- genWidth
         OSB.correct_xor n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_andPrecise" $
      do SW n <- genWidth
         OSB.correct_andPrecise n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_orPrecise" $
      do SW n <- genWidth
         OSB.correct_orPrecise n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  -- ** Concatenation, extension, selection, and truncation
  , genTest "correct_zero_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- OSB.genDomain w
                x <- genNatBV w
                pure (OSB.correct_zero_ext w c u x)
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- OSB.genDomain w
                x <- genNatBV w
                pure (OSB.correct_sign_ext w c u x)
  , genTest "correct_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- OSB.genDomain m
         x <- genNatBV m
         b <- OSB.genDomain n
         y <- genNatBV n
         pure (OSB.correct_concat m a x n b y)
  , genTest "correct_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         case testLeq (knownNat @1) w of
           Nothing -> error "impossible!"
           Just LeqProof -> do
             c <- OSB.genDomain w
             x <- genNatBV w
             pure (OSB.correct_select i n w c x)
  -- ** Shifts and rotations
  , genTest "correct_shl" $
      do SW n <- genWidth
         OSB.correct_shl n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_lshr" $
      do SW n <- genWidth
         OSB.correct_lshr n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_ashr" $
      do SW n <- genWidth
         OSB.correct_ashr n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_rol" $
      do SW n <- genWidth
         OSB.correct_rol n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_ror" $
      do SW n <- genWidth
         OSB.correct_ror n <$> OSB.genDomain n <*> genNatBV n <*> OSB.genDomain n <*> genNatBV n
  -- ** Lattice operations — *** Meets
  , genTest "correct_pseudoMeet" $
      do SW n <- genWidth
         OSB.correct_pseudoMeet n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_pseudoMeetPrecise" $
      do SW n <- genWidth
         OSB.correct_pseudoMeetPrecise n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetLowerBound" $
      do SW n <- genWidth
         OSB.pseudoMeetLowerBound n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetPreciseLowerBound" $
      do SW n <- genWidthSmall
         OSB.pseudoMeetPreciseLowerBound n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetCommutative" $
      do SW n <- genWidth
         OSB.pseudoMeetCommutative n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetPreciseCommutative" $
      do SW n <- genWidth
         OSB.pseudoMeetPreciseCommutative n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetIdempotent" $
      do SW n <- genWidth
         OSB.pseudoMeetIdempotent n <$> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetPreciseIdempotent" $
      do SW n <- genWidth
         OSB.pseudoMeetPreciseIdempotent n <$> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetTopIdentity" $
      do SW n <- genWidth
         OSB.pseudoMeetTopIdentity n <$> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetPreciseTopIdentity" $
      do SW n <- genWidth
         OSB.pseudoMeetPreciseTopIdentity n <$> OSB.genDomain n <*> genNatBV n
  -- *** Joins
  , genTest "correct_pseudoJoin" $
      do SW n <- genWidth
         OSB.correct_pseudoJoin n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "correct_pseudoJoinPrecise" $
      do SW n <- genWidth
         OSB.correct_pseudoJoinPrecise n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinUpperBound" $
      do SW n <- genWidth
         OSB.pseudoJoinUpperBound n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinPreciseUpperBound" $
      do SW n <- genWidthSmall
         OSB.pseudoJoinPreciseUpperBound n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinCommutative" $
      do SW n <- genWidth
         OSB.pseudoJoinCommutative n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinPreciseCommutative" $
      do SW n <- genWidth
         OSB.pseudoJoinPreciseCommutative n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinIdempotent" $
      do SW n <- genWidth
         OSB.pseudoJoinIdempotent n <$> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinPreciseIdempotent" $
      do SW n <- genWidth
         OSB.pseudoJoinPreciseIdempotent n <$> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinPreciseRefinesJoin" $
      do SW n <- genWidthSmall
         OSB.pseudoJoinPreciseRefinesJoin n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinTopAnnihilator" $
      do SW n <- genWidth
         OSB.pseudoJoinTopAnnihilator n <$> OSB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinPreciseTopAnnihilator" $
      do SW n <- genWidth
         OSB.pseudoJoinPreciseTopAnnihilator n <$> OSB.genDomain n <*> genNatBV n
  -- ** Branch-condition assumptions
  , genTest "correct_assumeUlt" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeUlt n a x b y)
  , genTest "correct_assumeUle" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeUle n a x b y)
  , genTest "correct_assumeUgt" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeUgt n a x b y)
  , genTest "correct_assumeUge" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeUge n a x b y)
  , genTest "correct_assumeSlt" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeSlt n a x b y)
  , genTest "correct_assumeSle" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeSle n a x b y)
  , genTest "correct_assumeSgt" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeSgt n a x b y)
  , genTest "correct_assumeSge" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeSge n a x b y)
  , genTest "correct_assumeSltPrecise" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeSltPrecise n a x b y)
  , genTest "correct_assumeSlePrecise" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeSlePrecise n a x b y)
  , genTest "correct_assumeSgtPrecise" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeSgtPrecise n a x b y)
  , genTest "correct_assumeSgePrecise" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeSgePrecise n a x b y)
  , genTest "correct_assumeEq" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeEq n a x b y)
  , genTest "correct_assumeNe" $
      do SW n <- genWidth
         (a, x) <- OSB.genPair n
         (b, y) <- OSB.genPair n
         pure (OSB.correct_assumeNe n a x b y)
  , genTest "assumeUltShrinks" $
      do SW n <- genWidth
         OSB.assumeUltShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeUleShrinks" $
      do SW n <- genWidth
         OSB.assumeUleShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeUgtShrinks" $
      do SW n <- genWidth
         OSB.assumeUgtShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeUgeShrinks" $
      do SW n <- genWidth
         OSB.assumeUgeShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeSltShrinks" $
      do SW n <- genWidth
         OSB.assumeSltShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeSleShrinks" $
      do SW n <- genWidth
         OSB.assumeSleShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeSgtShrinks" $
      do SW n <- genWidth
         OSB.assumeSgtShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeSgeShrinks" $
      do SW n <- genWidth
         OSB.assumeSgeShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeSltPreciseShrinks" $
      do SW n <- genWidth
         OSB.assumeSltPreciseShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeSlePreciseShrinks" $
      do SW n <- genWidth
         OSB.assumeSlePreciseShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeSgtPreciseShrinks" $
      do SW n <- genWidth
         OSB.assumeSgtPreciseShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeSgePreciseShrinks" $
      do SW n <- genWidth
         OSB.assumeSgePreciseShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeNeShrinks" $
      do SW n <- genWidth
         OSB.assumeNeShrinks n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "assumeSltPreciseIdempotent" $
      do SW n <- genWidth
         OSB.assumeSltPreciseIdempotent n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "assumeSlePreciseIdempotent" $
      do SW n <- genWidth
         OSB.assumeSlePreciseIdempotent n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "assumeSgtPreciseIdempotent" $
      do SW n <- genWidth
         OSB.assumeSgtPreciseIdempotent n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "assumeSgePreciseIdempotent" $
      do SW n <- genWidth
         OSB.assumeSgePreciseIdempotent n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  -- ** Internal helpers
  , genTest "gcdOddMatchesPrelude" $
      OSB.gcdOddMatchesPrelude <$> genNat <*> genNat
  , genTest "binGcdMatchesPrelude" $
      OSB.binGcdMatchesPrelude <$> genNat <*> genNat
  , genTest "nativeLeqPreciseMatchesBridge" $
      do SW n <- genWidth
         OSB.nativeLeqPreciseMatchesBridge n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "native2AdicMeetMatchesBridge" $
      do SW n <- genWidth
         OSB.native2AdicMeetMatchesBridge n <$> OSB.genDomain n <*> OSB.genDomain n <*> genNatBV n
  , genTest "nativeLeqExactMatchesBridge" $
      do SW n <- genWidth
         OSB.nativeLeqExactMatchesBridge n <$> OSB.genDomain n <*> OSB.genDomain n
  , genTest "nativeReduceMatchesBridge" $
      do SW n <- genWidth
         OSB.nativeReduceMatchesBridge n
           <$> OSB.genDomain n <*> B.genDomain n <*> genNatBV n
  ]

-- | An arbitrary 'Natural' over a wide range — large enough to exercise
-- many bit patterns and 2-adic valuations for the GCD properties.
genNat :: Gen Natural
genNat = fromInteger <$> chooseInteger (0, 2 ^ (64 :: Int) - 1)

-- | Generate a power-of-2 exponent in the range [0, w-1].
-- For a width w, 2^k where k < w will fit in the bitvector.
choosePow2Exp :: NatRepr w -> Gen Natural
choosePow2Exp w =
  do let maxExp = widthBits w - 1
     fromInteger <$> chooseInteger (0, toInteger maxExp)
  where
    widthBits :: NatRepr w -> Natural
    widthBits w' = go (maxUnsigned w' + 1)
      where
        go 1 = 0
        go n = 1 + go (n `Prelude.div` 2)

-- | Generate a power-of-2 value at width w.
genPow2Singleton :: NatRepr w -> Gen Natural
genPow2Singleton w =
  do k <- choosePow2Exp w
     pure ((2 :: Natural) ^ k)
