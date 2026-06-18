{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Geometric (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, isPosNat, someNat, testLeq, knownNat, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.Geometric as Geo
import           What4.Domains.Verification (Gen, chooseInt, chooseInteger, getSize)
import           VerifyBindings (genTest)

-- | A width @w@ with the evidence @3 <= w@ that the geometric domain requires.
data SomeWidth where
  SW :: (3 <= w) => NatRepr w -> SomeWidth

genWidth :: Gen SomeWidth
genWidth =
  do sz <- getSize
     x <- chooseInt (3, sz + 6)
     mkSW x

genWidthSmall :: Gen SomeWidth
genWidthSmall = chooseInt (3, 8) >>= mkSW

mkSW :: Int -> Gen SomeWidth
mkSW x =
  case someNat (fromIntegral x :: Natural) of
    Just (Some n)
      | Just LeqProof <- isPosNat n
      , Just LeqProof <- testLeq (knownNat @3) n -> pure (SW n)
    _ -> error "test panic! Geometric.mkSW"

genNatBV :: NatRepr w -> Gen Natural
genNatBV w = fromInteger <$> chooseInteger (0, maxUnsigned w)

tests :: TT.TestTree
tests = TT.testGroup "Geometric"
  [ -- Queries
    genTest "memberToList" $
      do SW n <- genWidthSmall
         Geo.memberToList n <$> Geo.genDomain n
  , genTest "toListMember" $
      do SW n <- genWidthSmall
         Geo.toListMember n <$> Geo.genDomain n <*> genNatBV n

    -- Arithmetic soundness (covers the zero-producing cases)
  , genTest "correct_neg" $
      do SW n <- genWidth
         Geo.correct_neg n <$> Geo.genDomain n <*> genNatBV n
  , genTest "correct_mul" $
      do SW n <- genWidth
         Geo.correct_mul n <$> Geo.genDomain n <*> genNatBV n <*> Geo.genDomain n <*> genNatBV n
  , genTest "correct_square" $
      do SW n <- genWidth
         Geo.correct_square n <$> Geo.genDomain n <*> genNatBV n
  , genTest "correct_pow" $
      do SW n <- genWidth
         Geo.correct_pow n <$> chooseInt (0, 10) <*> Geo.genDomain n <*> genNatBV n
  , genTest "correct_shl" $
      do SW n <- genWidth
         Geo.correct_shl n <$> chooseInt (0, 16) <*> Geo.genDomain n <*> genNatBV n

    -- Lattice soundness and laws
  , genTest "correct_pseudoJoin" $
      do SW n <- genWidth
         Geo.correct_pseudoJoin n <$> Geo.genDomain n <*> genNatBV n <*> Geo.genDomain n <*> genNatBV n
  , genTest "correct_pseudoMeet" $
      do SW n <- genWidth
         Geo.correct_pseudoMeet n <$> Geo.genDomain n <*> Geo.genDomain n <*> genNatBV n
  , genTest "leqReflexive" $
      do SW n <- genWidth
         Geo.leqReflexive n <$> Geo.genDomain n
  , genTest "leqTransitive" $
      do SW n <- genWidth
         Geo.leqTransitive n <$> Geo.genDomain n <*> Geo.genDomain n <*> Geo.genDomain n
  ]
