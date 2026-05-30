{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module WI (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, addNat, isPosNat, knownNat, someNat, testLeq, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.WI as W
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

genBV :: NatRepr w -> Gen Integer
genBV w = chooseInteger (0, maxUnsigned w)

-- | A short list of WIs at the given width, for the variadic 'pseudoJoinList'.
genDomainList :: NatRepr w -> Gen [W.Domain w]
genDomainList w = do
  k <- chooseInt (0, 5)
  sequence (replicate k (W.genDomain w))

-- | A constant shift amount in @[0, w]@.
genShift :: NatRepr w -> Gen Int
genShift w = chooseInt (0, fromIntegral (maxUnsigned w))

-- | An arbitrary nonnegative integer in @[0, 2^64)@, for tests parameterized
-- over a width exponent rather than a 'NatRepr'.
genIntBV :: Gen Integer
genIntBV = chooseInteger (0, 2 ^ (64 :: Int))

-- | Width exponent @k@ in @[1, sz + 4]@.
genWidthExp :: Gen Int
genWidthExp =
  do sz <- getSize
     chooseInt (1, sz + 4)

-- | Generate a 'W.Domain' that doesn't straddle the south pole, by drawing a
-- generic domain and 'ssplit'-ing it. Used for the @*Seg@ helpers'
-- preconditions.
genSsplitSegment :: NatRepr w -> Gen (W.Domain w)
genSsplitSegment w = do
  d <- W.genDomain w
  case W.ssplit w d of
    [] -> pure W.bottom
    [x] -> pure x
    (x : _) -> do
      i <- chooseInt (0, length (W.ssplit w d) - 1)
      pure (W.ssplit w d !! i)

-- | Like 'genSsplitSegment' but for the north pole.
genNsplitSegment :: NatRepr w -> Gen (W.Domain w)
genNsplitSegment w = do
  d <- W.genDomain w
  case W.nsplit w d of
    [] -> pure W.bottom
    [x] -> pure x
    (x : _) -> do
      i <- chooseInt (0, length (W.nsplit w d) - 1)
      pure (W.nsplit w d !! i)

tests :: TT.TestTree
tests = TT.testGroup "WI"
  [ -- Internal helpers
    genTest "circLeqAtZero" $
      W.circLeqAtZero <$> genIntBV <*> genIntBV <*> genWidthExp
  , genTest "circLeqAnchorMin" $
      W.circLeqAnchorMin <$> genIntBV <*> genIntBV <*> genWidthExp
  , genTest "circLeqAnchorMax" $
      W.circLeqAnchorMax <$> genIntBV <*> genIntBV <*> genWidthExp
  , genTest "msbHighBit" $
      W.msbHighBit <$> genIntBV <*> genWidthExp
  , genTest "removeZeroCovers" $
      do SW n <- genWidth
         W.removeZeroCovers n <$> W.genDomain n <*> genBV n
  , genTest "removeZeroNoZero" $
      do SW n <- genWidth
         W.removeZeroNoZero n <$> W.genDomain n
  , genTest "warrenAndSound" $
      W.warrenAndSound <$> genIntBV <*> genIntBV <*> genIntBV <*> genIntBV
                       <*> genWidthExp
  , genTest "warrenOrSound" $
      W.warrenOrSound <$> genIntBV <*> genIntBV <*> genIntBV <*> genIntBV
                      <*> genWidthExp
  , genTest "correct_udivSeg" $
      do SW n <- genWidth
         W.correct_udivSeg n <$> genSsplitSegment n <*> genBV n
                             <*> genSsplitSegment n <*> genBV n
  , genTest "correct_uremSeg" $
      do SW n <- genWidth
         W.correct_uremSeg n <$> genSsplitSegment n <*> genBV n
                             <*> genSsplitSegment n <*> genBV n
  , genTest "correct_sdivSeg" $
      do SW n <- genWidth
         W.correct_sdivSeg n <$> genNsplitSegment n <*> genBV n
                             <*> genNsplitSegment n <*> genBV n
  , genTest "correct_sremSeg" $
      do SW n <- genWidth
         W.correct_sremSeg n <$> genNsplitSegment n <*> genBV n
                             <*> genNsplitSegment n <*> genBV n
  , genTest "correct_bvAndSeg" $
      do SW n <- genWidth
         W.correct_bvAndSeg n <$> genSsplitSegment n <*> genBV n
                              <*> genSsplitSegment n <*> genBV n
  , genTest "correct_bvOrSeg" $
      do SW n <- genWidth
         W.correct_bvOrSeg n <$> genSsplitSegment n <*> genBV n
                             <*> genSsplitSegment n <*> genBV n
  , genTest "correct_bvXorSeg" $
      do SW n <- genWidth
         W.correct_bvXorSeg n <$> genSsplitSegment n <*> genBV n
                              <*> genSsplitSegment n <*> genBV n

    -- Construction
  , genTest "singletonMember" $
      do SW n <- genWidth
         W.singletonMember n <$> genBV n

    -- Queries
  , genTest "complementMember" $
      do SW n <- genWidth
         W.complementMember n <$> W.genDomain n <*> genBV n
  , genTest "subsetCorrect" $
      do SW n <- genWidth
         W.subsetCorrect n <$> W.genDomain n <*> W.genDomain n <*> genBV n
  , genTest "subsetReflexive" $
      do SW n <- genWidth
         W.subsetReflexive n <$> W.genDomain n
  , genTest "intersectCorrect" $
      do SW n <- genWidth
         W.intersectCorrect n <$> W.genDomain n <*> W.genDomain n <*> genBV n
  , genTest "pseudoJoinSound" $
      do SW n <- genWidth
         W.pseudoJoinSound n <$> W.genDomain n <*> W.genDomain n <*> genBV n
  , genTest "pseudoJoinListSound" $
      do SW n <- genWidth
         W.pseudoJoinListSound n <$> genDomainList n <*> genBV n
  , genTest "widenSound" $
      do SW n <- genWidth
         W.widenSound n <$> W.genDomain n <*> W.genDomain n <*> genBV n

    -- Splits
  , genTest "nsplitCovers" $
      do SW n <- genWidth
         W.nsplitCovers n <$> W.genDomain n <*> genBV n
  , genTest "nsplitNotStraddleNP" $
      do SW n <- genWidth
         W.nsplitNotStraddleNP n <$> W.genDomain n
  , genTest "ssplitCovers" $
      do SW n <- genWidth
         W.ssplitCovers n <$> W.genDomain n <*> genBV n
  , genTest "ssplitNotStraddleSP" $
      do SW n <- genWidth
         W.ssplitNotStraddleSP n <$> W.genDomain n
  , genTest "cutCovers" $
      do SW n <- genWidth
         W.cutCovers n <$> W.genDomain n <*> genBV n
  , genTest "cutNotStraddlePoles" $
      do SW n <- genWidth
         W.cutNotStraddlePoles n <$> W.genDomain n

    -- Arithmetic
  , genTest "correct_neg" $
      do SW n <- genWidth
         W.correct_neg n <$> W.genDomain n <*> genBV n
  , genTest "correct_add" $
      do SW n <- genWidth
         W.correct_add n <$> W.genDomain n <*> genBV n
                         <*> W.genDomain n <*> genBV n
  , genTest "correct_sub" $
      do SW n <- genWidth
         W.correct_sub n <$> W.genDomain n <*> genBV n
                         <*> W.genDomain n <*> genBV n
  , genTest "correct_umul" $
      do SW n <- genWidth
         W.correct_umul n <$> W.genDomain n <*> genBV n
                          <*> W.genDomain n <*> genBV n
  , genTest "correct_smul" $
      do SW n <- genWidth
         W.correct_smul n <$> W.genDomain n <*> genBV n
                          <*> W.genDomain n <*> genBV n
  , genTest "correct_usmul" $
      do SW n <- genWidth
         W.correct_usmul n <$> W.genDomain n <*> genBV n
                           <*> W.genDomain n <*> genBV n
  , genTest "correct_mul" $
      do SW n <- genWidth
         W.correct_mul n <$> W.genDomain n <*> genBV n
                         <*> W.genDomain n <*> genBV n
  , genTest "correct_udiv" $
      do SW n <- genWidth
         W.correct_udiv n <$> W.genDomain n <*> genBV n
                          <*> W.genDomain n <*> genBV n
  , genTest "correct_urem" $
      do SW n <- genWidth
         W.correct_urem n <$> W.genDomain n <*> genBV n
                          <*> W.genDomain n <*> genBV n
  , genTest "correct_sdiv" $
      do SW n <- genWidth
         W.correct_sdiv n <$> W.genDomain n <*> genBV n
                          <*> W.genDomain n <*> genBV n
  , genTest "correct_srem" $
      do SW n <- genWidth
         W.correct_srem n <$> W.genDomain n <*> genBV n
                          <*> W.genDomain n <*> genBV n

    -- Bitwise operations
  , genTest "correct_not" $
      do SW n <- genWidth
         W.correct_not n <$> W.genDomain n <*> genBV n
  , genTest "correct_and" $
      do SW n <- genWidth
         W.correct_and n <$> W.genDomain n <*> genBV n
                         <*> W.genDomain n <*> genBV n
  , genTest "correct_or" $
      do SW n <- genWidth
         W.correct_or n <$> W.genDomain n <*> genBV n
                        <*> W.genDomain n <*> genBV n
  , genTest "correct_xor" $
      do SW n <- genWidth
         W.correct_xor n <$> W.genDomain n <*> genBV n
                         <*> W.genDomain n <*> genBV n

    -- Concatenation, extension, selection, and truncation
  , genTest "correct_zero_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- W.genDomain w
                x <- genBV w
                pure (W.correct_zero_ext w c u x)
  , genTest "correct_sign_ext" $
      do SW w <- genWidth
         SW n <- genWidth
         let u = addNat w n
         case testLeq (addNat w (knownNat @1)) u of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- W.genDomain w
                x <- genBV w
                pure (W.correct_sign_ext w c u x)
  , genTest "correct_trunc" $
      do SW n <- genWidth
         SW m <- genWidth
         let w = addNat n m
         case testLeq (addNat n (knownNat @1)) w of
           Nothing -> error "impossible!"
           Just LeqProof ->
             do c <- W.genDomain w
                x <- genBV w
                pure (W.correct_trunc n w c x)

    -- Shifts and rotations
  , genTest "correct_shl" $
      do SW n <- genWidth
         W.correct_shl n <$> W.genDomain n <*> genBV n <*> genShift n
  , genTest "correct_lshr" $
      do SW n <- genWidth
         W.correct_lshr n <$> W.genDomain n <*> genBV n <*> genShift n
  , genTest "correct_ashr" $
      do SW n <- genWidth
         W.correct_ashr n <$> W.genDomain n <*> genBV n <*> genShift n
  ]
