{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module StridesBitwise (tests) where

import qualified Test.Tasty as TT

import qualified Data.List as List
import           Data.Parameterized.NatRepr (NatRepr, addNat, addIsLeq, isPosNat, knownNat, someNat, testLeq, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import qualified What4.Domains.BV.StridesBitwise as SB
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

genIntegerBV :: NatRepr w -> Gen Integer
genIntegerBV w = chooseInteger (0, maxUnsigned w)

tests :: TT.TestTree
tests = TT.testGroup "StridesBitwise"
  [ -- ** Construction
    genTest "fromAscEltListMember" $
      do SW n <- genWidth
         SB.fromAscEltListMember n <$> genAscNatList n
  -- ** Canonicalization
  , genTest "canonLossless" $
      do SW n <- genWidth
         SB.canonLossless n <$> SB.genDomain n <*> genNatBV n
  , genTest "canonProper" $
      do SW n <- genWidth
         SB.canonProper n <$> SB.genDomain n
  , genTest "canonIdempotent" $
      do SW n <- genWidth
         SB.canonIdempotent n <$> SB.genDomain n <*> genNatBV n
  -- ** Conversion
  , genTest "toArithCorrect" $
      do SW n <- genWidth
         SB.toArithCorrect n <$> SB.genDomain n <*> genNatBV n
  , genTest "fromArithCorrect" $
      do SW n <- genWidth
         SB.fromArithCorrect n <$> A.genDomain n <*> genNatBV n
  , genTest "roundtripArith" $
      do SW n <- genWidthSmall
         SB.roundtripArith n <$> SB.genDomain n
  , genTest "toBitwiseCorrect" $
      do SW n <- genWidth
         SB.toBitwiseCorrect n <$> SB.genDomain n <*> genNatBV n
  , genTest "forcedBitsMember" $
      do SW n <- genWidth
         SB.forcedBitsMember n <$> SB.genDomain n <*> genNatBV n
  , genTest "fromBitwiseCorrect" $
      do SW n <- genWidth
         SB.fromBitwiseCorrect n <$> B.genDomain n <*> genNatBV n
  -- ** Queries
  , genTest "toListMember" $
      do SW n <- genWidthSmall
         SB.toListMember n <$> SB.genDomain n
  , genTest "memberToList" $
      do SW n <- genWidthSmall
         SB.memberToList n <$> SB.genDomain n <*> genNatBV n
  , genTest "toListNoDuplicates" $
      do SW n <- genWidthSmall
         SB.toListNoDuplicates n <$> SB.genDomain n
  , genTest "leqCorrect" $
      do SW n <- genWidthSmall
         SB.leqCorrect n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "leqReflexive" $
      do SW n <- genWidth
         SB.leqReflexive n <$> SB.genDomain n
  , genTest "leqTransitive" $
      do SW n <- genWidth
         SB.leqTransitive n <$> SB.genDomain n <*> SB.genDomain n <*> SB.genDomain n
  , genTest "leqPreciseCorrect" $
      do SW n <- genWidthSmall
         SB.leqPreciseCorrect n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "leqPreciseReflexive" $
      do SW n <- genWidth
         SB.leqPreciseReflexive n <$> SB.genDomain n
  , genTest "sizeViaToList" $
      do SW n <- genWidthSmall
         SB.sizeViaToList n <$> SB.genDomain n
  , genTest "sizeAtMostComponents" $
      do SW n <- genWidth
         SB.sizeAtMostComponents n <$> SB.genDomain n
  , genTest "sizeExactCorrect" $
      do SW n <- genWidthSmall
         SB.sizeExactCorrect n <$> SB.genDomain n
  , genTest "windowMarginalCount" $
      do SW n <- genWidthSmall
         SB.windowMarginalCount n <$> SB.genDomain n
  , genTest "uniformWindowBalanced" $
      do SW n <- genWidthSmall
         SB.uniformWindowBalanced n <$> SB.genDomain n
  , genTest "pinsConflictEmpty" $
      do SW n <- genWidthSmall
         SB.pinsConflictEmpty n <$> SB.genDomain n <*> SB.genDomain n
  -- ** Arithmetic
  , genTest "correct_neg" $
      do SW n <- genWidth
         SB.correct_neg n <$> SB.genDomain n <*> genNatBV n
  , genTest "correct_add" $
      do SW n <- genWidth
         SB.correct_add n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_sub" $
      do SW n <- genWidth
         SB.correct_sub n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_scale" $
      do SW n <- genWidth
         SB.correct_scale n <$> chooseInteger (-100, 100) <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_mul" $
      do SW n <- genWidth
         SB.correct_mul n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_mulPrecise" $
      do SW n <- genWidth
         SB.correct_mulPrecise n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         SB.correct_udiv n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_udivPrecise" $
      do SW n <- genWidth
         SB.correct_udivPrecise n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_urem" $
      do SW n <- genWidth
         SB.correct_urem n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_uremPrecise" $
      do SW n <- genWidth
         SB.correct_uremPrecise n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         SB.correct_sdiv n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_srem" $
      do SW n <- genWidth
         SB.correct_srem n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "addExact" $
      do SW n <- genWidth
         SB.addExact n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "subExact" $
      do SW n <- genWidth
         SB.subExact n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "mulConstExact" $
      do SW n <- genWidth
         SB.mulConstExact n <$> chooseInteger (-100, 100) <*> SB.genDomain n
  , genTest "udivConstExact" $
      do SW n <- genWidth
         SB.udivConstExact n <$> SB.genDomain n <*> genNatBV n
  , genTest "uremConstExact" $
      do SW n <- genWidth
         SB.uremConstExact n <$> SB.genDomain n <*> genNatBV n
  , genTest "ultExactTrueSeparated" $
      do SW n <- genWidth
         SB.ultExactTrueSeparated n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "ultExactFalseSeparated" $
      do SW n <- genWidth
         SB.ultExactFalseSeparated n <$> SB.genDomain n <*> SB.genDomain n
  -- *** Arithmetic (SMT-LIB div-by-zero semantics)
  , genTest "correct_udivSmtlib" $
      do SW n <- genWidth
         SB.correct_udivSmtlib n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_uremSmtlib" $
      do SW n <- genWidth
         SB.correct_uremSmtlib n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_sdivSmtlib" $
      do SW n <- genWidth
         SB.correct_sdivSmtlib n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_sremSmtlib" $
      do SW n <- genWidth
         SB.correct_sremSmtlib n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  -- ** Bitwise operations
  , genTest "correct_not" $
      do SW n <- genWidth
         SB.correct_not n <$> SB.genDomain n <*> genNatBV n
  , genTest "correct_and" $
      do SW n <- genWidth
         SB.correct_and n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_or" $
      do SW n <- genWidth
         SB.correct_or n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_xor" $
      do SW n <- genWidth
         SB.correct_xor n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_andPrecise" $
      do SW n <- genWidth
         SB.correct_andPrecise n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_orPrecise" $
      do SW n <- genWidth
         SB.correct_orPrecise n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  -- ** Concatenation, extension, selection, and truncation
  , genTest "correct_zero_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- SB.genDomain w
                x <- genNatBV w
                pure (SB.correct_zero_ext w c u x)
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- SB.genDomain w
                x <- genNatBV w
                pure (SB.correct_sign_ext w c u x)
  , genTest "correct_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- SB.genDomain m
         x <- genNatBV m
         b <- SB.genDomain n
         y <- genNatBV n
         pure (SB.correct_concat m a x n b y)
  , genTest "correct_select" $
      do SW n <- genWidth
         SW i <- genWidth
         SW z <- genWidth
         let i_n = addNat i n
         let w = addNat i_n z
         LeqProof <- pure (addIsLeq i_n z)
         -- @1 <= w@ from @1 <= z@ and @addLeqOnRight@.
         case testLeq (knownNat @1) w of
           Nothing -> error "impossible!"
           Just LeqProof -> do
             c <- SB.genDomain w
             x <- genNatBV w
             pure (SB.correct_select i n w c x)
  -- ** Shifts and rotations
  , genTest "correct_shl" $
      do SW n <- genWidth
         SB.correct_shl n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_lshr" $
      do SW n <- genWidth
         SB.correct_lshr n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_ashr" $
      do SW n <- genWidth
         SB.correct_ashr n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_rol" $
      do SW n <- genWidth
         SB.correct_rol n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_ror" $
      do SW n <- genWidth
         SB.correct_ror n <$> SB.genDomain n <*> genNatBV n <*> SB.genDomain n <*> genNatBV n
  -- ** Lattice operations — *** Meets
  , genTest "correct_pseudoMeet" $
      do SW n <- genWidth
         SB.correct_pseudoMeet n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_pseudoMeetPrecise" $
      do SW n <- genWidth
         SB.correct_pseudoMeetPrecise n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetLowerBound" $
      do SW n <- genWidth
         SB.pseudoMeetLowerBound n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetPreciseLowerBound" $
      do SW n <- genWidthSmall
         SB.pseudoMeetPreciseLowerBound n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetCommutative" $
      do SW n <- genWidth
         SB.pseudoMeetCommutative n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetPreciseCommutative" $
      do SW n <- genWidth
         SB.pseudoMeetPreciseCommutative n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetIdempotent" $
      do SW n <- genWidth
         SB.pseudoMeetIdempotent n <$> SB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetPreciseIdempotent" $
      do SW n <- genWidth
         SB.pseudoMeetPreciseIdempotent n <$> SB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetTopIdentity" $
      do SW n <- genWidth
         SB.pseudoMeetTopIdentity n <$> SB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetPreciseTopIdentity" $
      do SW n <- genWidth
         SB.pseudoMeetPreciseTopIdentity n <$> SB.genDomain n <*> genNatBV n
  -- *** Joins
  , genTest "correct_pseudoJoin" $
      do SW n <- genWidth
         SB.correct_pseudoJoin n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "correct_pseudoJoinPrecise" $
      do SW n <- genWidth
         SB.correct_pseudoJoinPrecise n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinUpperBound" $
      do SW n <- genWidth
         SB.pseudoJoinUpperBound n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinPreciseUpperBound" $
      do SW n <- genWidthSmall
         SB.pseudoJoinPreciseUpperBound n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinCommutative" $
      do SW n <- genWidth
         SB.pseudoJoinCommutative n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinPreciseCommutative" $
      do SW n <- genWidth
         SB.pseudoJoinPreciseCommutative n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinIdempotent" $
      do SW n <- genWidth
         SB.pseudoJoinIdempotent n <$> SB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinPreciseIdempotent" $
      do SW n <- genWidth
         SB.pseudoJoinPreciseIdempotent n <$> SB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinPreciseRefinesJoin" $
      do SW n <- genWidthSmall
         SB.pseudoJoinPreciseRefinesJoin n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinTopAnnihilator" $
      do SW n <- genWidth
         SB.pseudoJoinTopAnnihilator n <$> SB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinPreciseTopAnnihilator" $
      do SW n <- genWidth
         SB.pseudoJoinPreciseTopAnnihilator n <$> SB.genDomain n <*> genNatBV n
  -- ** Branch-condition assumptions
  --
  -- Witnesses are drawn with 'genPair' (element from the domain) rather
  -- than independently, so @member a x@\/@member b y@ hold by construction.
  -- The reduced product is far sparser than either component, so an
  -- independent draw would discard almost every case (and Hedgehog gives
  -- up after a fixed discard budget); this leaves only the comparison
  -- @x \`op\` y@ to discard.
  , genTest "correct_assumeUlt" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeUlt n a x b y)
  , genTest "correct_assumeUle" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeUle n a x b y)
  , genTest "correct_assumeUgt" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeUgt n a x b y)
  , genTest "correct_assumeUge" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeUge n a x b y)
  , genTest "correct_assumeSlt" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeSlt n a x b y)
  , genTest "correct_assumeSle" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeSle n a x b y)
  , genTest "correct_assumeSgt" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeSgt n a x b y)
  , genTest "correct_assumeSge" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeSge n a x b y)
  , genTest "correct_assumeSltPrecise" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeSltPrecise n a x b y)
  , genTest "correct_assumeSlePrecise" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeSlePrecise n a x b y)
  , genTest "correct_assumeSgtPrecise" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeSgtPrecise n a x b y)
  , genTest "correct_assumeSgePrecise" $
      do SW n <- genWidth
         (a, x) <- SB.genPair n
         (b, y) <- SB.genPair n
         pure (SB.correct_assumeSgePrecise n a x b y)
  , genTest "assumeUltShrinks" $
      do SW n <- genWidth
         SB.assumeUltShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeUleShrinks" $
      do SW n <- genWidth
         SB.assumeUleShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeUgtShrinks" $
      do SW n <- genWidth
         SB.assumeUgtShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeUgeShrinks" $
      do SW n <- genWidth
         SB.assumeUgeShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeSltShrinks" $
      do SW n <- genWidth
         SB.assumeSltShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeSleShrinks" $
      do SW n <- genWidth
         SB.assumeSleShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeSgtShrinks" $
      do SW n <- genWidth
         SB.assumeSgtShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeSgeShrinks" $
      do SW n <- genWidth
         SB.assumeSgeShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeSltPreciseShrinks" $
      do SW n <- genWidth
         SB.assumeSltPreciseShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeSlePreciseShrinks" $
      do SW n <- genWidth
         SB.assumeSlePreciseShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeSgtPreciseShrinks" $
      do SW n <- genWidth
         SB.assumeSgtPreciseShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeSgePreciseShrinks" $
      do SW n <- genWidth
         SB.assumeSgePreciseShrinks n <$> SB.genDomain n <*> SB.genDomain n
  , genTest "assumeSltPreciseIdempotent" $
      do SW n <- genWidth
         SB.assumeSltPreciseIdempotent n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "assumeSlePreciseIdempotent" $
      do SW n <- genWidth
         SB.assumeSlePreciseIdempotent n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "assumeSgtPreciseIdempotent" $
      do SW n <- genWidth
         SB.assumeSgtPreciseIdempotent n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  , genTest "assumeSgePreciseIdempotent" $
      do SW n <- genWidth
         SB.assumeSgePreciseIdempotent n <$> SB.genDomain n <*> SB.genDomain n <*> genNatBV n
  ]
