{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SmoothClpBitwise (tests) where

import qualified Test.Tasty as TT

import qualified Data.List as List
import           Data.Parameterized.NatRepr (NatRepr, addNat, addIsLeq, isPosNat, knownNat, someNat, testLeq, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import qualified What4.Domains.BV.SmoothClpBitwise as SCB
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
tests = TT.testGroup "SmoothClpBitwise"
  [ -- ** Construction
    genTest "fromAscEltListMember" $
      do SW n <- genWidth
         SCB.fromAscEltListMember n <$> genAscNatList n
  -- ** Canonicalization
  , genTest "canonLossless" $
      do SW n <- genWidth
         SCB.canonLossless n <$> SCB.genDomain n <*> genNatBV n
  , genTest "canonProper" $
      do SW n <- genWidth
         SCB.canonProper n <$> SCB.genDomain n
  , genTest "canonIdempotent" $
      do SW n <- genWidth
         SCB.canonIdempotent n <$> SCB.genDomain n <*> genNatBV n
  -- ** Conversion
  , genTest "toArithCorrect" $
      do SW n <- genWidth
         SCB.toArithCorrect n <$> SCB.genDomain n <*> genNatBV n
  , genTest "fromArithCorrect" $
      do SW n <- genWidth
         SCB.fromArithCorrect n <$> A.genDomain n <*> genNatBV n
  , genTest "roundtripArith" $
      do SW n <- genWidthSmall
         SCB.roundtripArith n <$> SCB.genDomain n
  , genTest "toBitwiseCorrect" $
      do SW n <- genWidth
         SCB.toBitwiseCorrect n <$> SCB.genDomain n <*> genNatBV n
  , genTest "forcedBitsMember" $
      do SW n <- genWidth
         SCB.forcedBitsMember n <$> SCB.genDomain n <*> genNatBV n
  , genTest "fromBitwiseCorrect" $
      do SW n <- genWidth
         SCB.fromBitwiseCorrect n <$> B.genDomain n <*> genNatBV n
  -- ** Queries
  , genTest "toListMember" $
      do SW n <- genWidthSmall
         SCB.toListMember n <$> SCB.genDomain n
  , genTest "memberToList" $
      do SW n <- genWidthSmall
         SCB.memberToList n <$> SCB.genDomain n <*> genNatBV n
  , genTest "toListNoDuplicates" $
      do SW n <- genWidthSmall
         SCB.toListNoDuplicates n <$> SCB.genDomain n
  , genTest "leqCorrect" $
      do SW n <- genWidthSmall
         SCB.leqCorrect n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTest "leqReflexive" $
      do SW n <- genWidth
         SCB.leqReflexive n <$> SCB.genDomain n
  , genTestFew "leqTransitive" $
      do SW n <- genWidth
         SCB.leqTransitive n <$> SCB.genDomain n <*> SCB.genDomain n <*> SCB.genDomain n
  , genTestFew "leqPreciseCorrect" $
      do SW n <- genWidthSmall
         SCB.leqPreciseCorrect n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTestFew "leqPreciseReflexive" $
      do SW n <- genWidth
         SCB.leqPreciseReflexive n <$> SCB.genDomain n
  , genTest "sizeViaToList" $
      do SW n <- genWidthSmall
         SCB.sizeViaToList n <$> SCB.genDomain n
  , genTest "sizeAtMostComponents" $
      do SW n <- genWidth
         SCB.sizeAtMostComponents n <$> SCB.genDomain n
  , genTestFew "sizeExactCorrect" $
      do SW n <- genWidthSmall
         SCB.sizeExactCorrect n <$> SCB.genDomain n
  , genTest "windowMarginalCount" $
      do SW n <- genWidthSmall
         SCB.windowMarginalCount n <$> SCB.genDomain n
  , genTest "uniformWindowBalanced" $
      do SW n <- genWidthSmall
         SCB.uniformWindowBalanced n <$> SCB.genDomain n
  , genTest "pinsConflictEmpty" $
      do SW n <- genWidthSmall
         SCB.pinsConflictEmpty n <$> SCB.genDomain n <*> SCB.genDomain n
  -- ** Arithmetic
  , genTest "correct_neg" $
      do SW n <- genWidth
         SCB.correct_neg n <$> SCB.genDomain n <*> genNatBV n
  , genTest "correct_add" $
      do SW n <- genWidth
         SCB.correct_add n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_sub" $
      do SW n <- genWidth
         SCB.correct_sub n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_scale" $
      do SW n <- genWidth
         SCB.correct_scale n <$> chooseInteger (-100, 100) <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_mul" $
      do SW n <- genWidth
         SCB.correct_mul n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "correct_mulPrecise" $
      do SW n <- genWidth
         SCB.correct_mulPrecise n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         SCB.correct_udiv n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "correct_udivPrecise" $
      do SW n <- genWidth
         SCB.correct_udivPrecise n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_urem" $
      do SW n <- genWidth
         SCB.correct_urem n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "correct_uremPrecise" $
      do SW n <- genWidth
         SCB.correct_uremPrecise n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         SCB.correct_sdiv n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_srem" $
      do SW n <- genWidth
         SCB.correct_srem n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "addExact" $
      do SW n <- genWidth
         SCB.addExact n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTestFew "subExact" $
      do SW n <- genWidth
         SCB.subExact n <$> SCB.genDomain n <*> SCB.genDomain n
  -- mulConstExact removed under smoothing (see SmoothClp.hs)
  , genTestFew "udivConstExact" $
      do SW n <- genWidth
         SCB.udivConstExact n <$> SCB.genDomain n <*> genNatBV n
  , genTestFew "uremConstExact" $
      do SW n <- genWidth
         SCB.uremConstExact n <$> SCB.genDomain n <*> genNatBV n
  , genTestFew "ultExactTrueSeparated" $
      do SW n <- genWidth
         SCB.ultExactTrueSeparated n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTestFew "ultExactFalseSeparated" $
      do SW n <- genWidth
         SCB.ultExactFalseSeparated n <$> SCB.genDomain n <*> SCB.genDomain n
  -- *** Arithmetic (SMT-LIB div-by-zero semantics)
  , genTest "correct_udivSmtlib" $
      do SW n <- genWidth
         SCB.correct_udivSmtlib n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_uremSmtlib" $
      do SW n <- genWidth
         SCB.correct_uremSmtlib n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_sdivSmtlib" $
      do SW n <- genWidth
         SCB.correct_sdivSmtlib n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_sremSmtlib" $
      do SW n <- genWidth
         SCB.correct_sremSmtlib n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  -- ** Arithmetic (LLVM overflow flags)
  , genTest "correct_addNuw" $
      do SW n <- genWidth
         SCB.correct_addNuw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_addNsw" $
      do SW n <- genWidth
         SCB.correct_addNsw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_addNswNuw" $
      do SW n <- genWidth
         SCB.correct_addNswNuw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_subNuw" $
      do SW n <- genWidth
         SCB.correct_subNuw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_subNsw" $
      do SW n <- genWidth
         SCB.correct_subNsw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_subNswNuw" $
      do SW n <- genWidth
         SCB.correct_subNswNuw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_mulNuw" $
      do SW n <- genWidth
         SCB.correct_mulNuw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_mulNsw" $
      do SW n <- genWidth
         SCB.correct_mulNsw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_mulNswNuw" $
      do SW n <- genWidth
         SCB.correct_mulNswNuw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_shlNuw" $
      do SW n <- genWidth
         SCB.correct_shlNuw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_shlNsw" $
      do SW n <- genWidth
         SCB.correct_shlNsw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_shlNswNuw" $
      do SW n <- genWidth
         SCB.correct_shlNswNuw n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "correct_udivExact" $
      do SW n <- genWidth
         SCB.correct_udivExact n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "correct_sdivExact" $
      do SW n <- genWidth
         SCB.correct_sdivExact n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "correct_lshrExact" $
      do SW n <- genWidth
         SCB.correct_lshrExact n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "correct_ashrExact" $
      do SW n <- genWidth
         SCB.correct_ashrExact n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  -- ** Bitwise operations
  , genTest "correct_not" $
      do SW n <- genWidth
         SCB.correct_not n <$> SCB.genDomain n <*> genNatBV n
  , genTest "correct_and" $
      do SW n <- genWidth
         SCB.correct_and n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_or" $
      do SW n <- genWidth
         SCB.correct_or n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_xor" $
      do SW n <- genWidth
         SCB.correct_xor n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "correct_andPrecise" $
      do SW n <- genWidth
         SCB.correct_andPrecise n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "correct_orPrecise" $
      do SW n <- genWidth
         SCB.correct_orPrecise n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  -- ** Concatenation, extension, selection, and truncation
  , genTest "correct_zero_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- SCB.genDomain w
                x <- genNatBV w
                pure (SCB.correct_zero_ext w c u x)
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- SCB.genDomain w
                x <- genNatBV w
                pure (SCB.correct_sign_ext w c u x)
  , genTest "correct_concat" $
      do SW m <- genWidth
         SW n <- genWidth
         a <- SCB.genDomain m
         x <- genNatBV m
         b <- SCB.genDomain n
         y <- genNatBV n
         pure (SCB.correct_concat m a x n b y)
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
             c <- SCB.genDomain w
             x <- genNatBV w
             pure (SCB.correct_select i n w c x)
  -- ** Shifts and rotations
  , genTest "correct_shl" $
      do SW n <- genWidth
         SCB.correct_shl n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_lshr" $
      do SW n <- genWidth
         SCB.correct_lshr n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_ashr" $
      do SW n <- genWidth
         SCB.correct_ashr n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_rol" $
      do SW n <- genWidth
         SCB.correct_rol n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  , genTest "correct_ror" $
      do SW n <- genWidth
         SCB.correct_ror n <$> SCB.genDomain n <*> genNatBV n <*> SCB.genDomain n <*> genNatBV n
  -- ** Lattice operations — *** Meets
  , genTest "correct_pseudoMeet" $
      do SW n <- genWidth
         SCB.correct_pseudoMeet n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "correct_pseudoMeetPrecise" $
      do SW n <- genWidth
         SCB.correct_pseudoMeetPrecise n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetLowerBound" $
      do SW n <- genWidth
         SCB.pseudoMeetLowerBound n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "pseudoMeetPreciseLowerBound" $
      do SW n <- genWidthSmall
         SCB.pseudoMeetPreciseLowerBound n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetCommutative" $
      do SW n <- genWidth
         SCB.pseudoMeetCommutative n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "pseudoMeetPreciseCommutative" $
      do SW n <- genWidth
         SCB.pseudoMeetPreciseCommutative n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetIdempotent" $
      do SW n <- genWidth
         SCB.pseudoMeetIdempotent n <$> SCB.genDomain n <*> genNatBV n
  , genTestFew "pseudoMeetPreciseIdempotent" $
      do SW n <- genWidth
         SCB.pseudoMeetPreciseIdempotent n <$> SCB.genDomain n <*> genNatBV n
  , genTest "pseudoMeetTopIdentity" $
      do SW n <- genWidth
         SCB.pseudoMeetTopIdentity n <$> SCB.genDomain n <*> genNatBV n
  , genTestFew "pseudoMeetPreciseTopIdentity" $
      do SW n <- genWidth
         SCB.pseudoMeetPreciseTopIdentity n <$> SCB.genDomain n <*> genNatBV n
  -- *** Joins
  , genTest "correct_pseudoJoin" $
      do SW n <- genWidth
         SCB.correct_pseudoJoin n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "correct_pseudoJoinPrecise" $
      do SW n <- genWidth
         SCB.correct_pseudoJoinPrecise n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinUpperBound" $
      do SW n <- genWidth
         SCB.pseudoJoinUpperBound n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "pseudoJoinPreciseUpperBound" $
      do SW n <- genWidthSmall
         SCB.pseudoJoinPreciseUpperBound n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinCommutative" $
      do SW n <- genWidth
         SCB.pseudoJoinCommutative n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "pseudoJoinPreciseCommutative" $
      do SW n <- genWidth
         SCB.pseudoJoinPreciseCommutative n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinIdempotent" $
      do SW n <- genWidth
         SCB.pseudoJoinIdempotent n <$> SCB.genDomain n <*> genNatBV n
  , genTestFew "pseudoJoinPreciseIdempotent" $
      do SW n <- genWidth
         SCB.pseudoJoinPreciseIdempotent n <$> SCB.genDomain n <*> genNatBV n
  , genTestFew "pseudoJoinPreciseRefinesJoin" $
      do SW n <- genWidthSmall
         SCB.pseudoJoinPreciseRefinesJoin n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTest "pseudoJoinTopAnnihilator" $
      do SW n <- genWidth
         SCB.pseudoJoinTopAnnihilator n <$> SCB.genDomain n <*> genNatBV n
  , genTestFew "pseudoJoinPreciseTopAnnihilator" $
      do SW n <- genWidth
         SCB.pseudoJoinPreciseTopAnnihilator n <$> SCB.genDomain n <*> genNatBV n
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
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeUlt n a x b y)
  , genTest "correct_assumeUle" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeUle n a x b y)
  , genTest "correct_assumeUgt" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeUgt n a x b y)
  , genTest "correct_assumeUge" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeUge n a x b y)
  , genTest "correct_assumeSlt" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeSlt n a x b y)
  , genTest "correct_assumeSle" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeSle n a x b y)
  , genTest "correct_assumeSgt" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeSgt n a x b y)
  , genTest "correct_assumeSge" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeSge n a x b y)
  , genTestFew "correct_assumeSltPrecise" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeSltPrecise n a x b y)
  , genTestFew "correct_assumeSlePrecise" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeSlePrecise n a x b y)
  , genTestFew "correct_assumeSgtPrecise" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeSgtPrecise n a x b y)
  , genTestFew "correct_assumeSgePrecise" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeSgePrecise n a x b y)
  , genTest "correct_assumeEq" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeEq n a x b y)
  , genTest "correct_assumeNe" $
      do SW n <- genWidth
         (a, x) <- SCB.genPair n
         (b, y) <- SCB.genPair n
         pure (SCB.correct_assumeNe n a x b y)
  , genTest "assumeUltShrinks" $
      do SW n <- genWidth
         SCB.assumeUltShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTest "assumeUleShrinks" $
      do SW n <- genWidth
         SCB.assumeUleShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTest "assumeUgtShrinks" $
      do SW n <- genWidth
         SCB.assumeUgtShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTest "assumeUgeShrinks" $
      do SW n <- genWidth
         SCB.assumeUgeShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTest "assumeSltShrinks" $
      do SW n <- genWidth
         SCB.assumeSltShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTest "assumeSleShrinks" $
      do SW n <- genWidth
         SCB.assumeSleShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTest "assumeSgtShrinks" $
      do SW n <- genWidth
         SCB.assumeSgtShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTest "assumeSgeShrinks" $
      do SW n <- genWidth
         SCB.assumeSgeShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTestFew "assumeSltPreciseShrinks" $
      do SW n <- genWidth
         SCB.assumeSltPreciseShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTestFew "assumeSlePreciseShrinks" $
      do SW n <- genWidth
         SCB.assumeSlePreciseShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTestFew "assumeSgtPreciseShrinks" $
      do SW n <- genWidth
         SCB.assumeSgtPreciseShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTestFew "assumeSgePreciseShrinks" $
      do SW n <- genWidth
         SCB.assumeSgePreciseShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTest "assumeNeShrinks" $
      do SW n <- genWidth
         SCB.assumeNeShrinks n <$> SCB.genDomain n <*> SCB.genDomain n
  , genTestFew "assumeSltPreciseIdempotent" $
      do SW n <- genWidth
         SCB.assumeSltPreciseIdempotent n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "assumeSlePreciseIdempotent" $
      do SW n <- genWidth
         SCB.assumeSlePreciseIdempotent n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "assumeSgtPreciseIdempotent" $
      do SW n <- genWidth
         SCB.assumeSgtPreciseIdempotent n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  , genTestFew "assumeSgePreciseIdempotent" $
      do SW n <- genWidth
         SCB.assumeSgePreciseIdempotent n <$> SCB.genDomain n <*> SCB.genDomain n <*> genNatBV n
  ]
