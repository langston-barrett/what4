{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module GeoStrides (tests) where

import qualified Test.Tasty as TT

import           Data.Parameterized.NatRepr (NatRepr, isPosNat, someNat, testLeq, knownNat, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.GeoStrides as G
import           What4.Domains.Verification (Gen, chooseInt, chooseInteger, getSize)
import           VerifyBindings (genTest)

-- | A width @w@ with the evidence @3 <= w@ that the geometric domain requires.
data SomeWidth where
  SW :: (3 <= w) => NatRepr w -> SomeWidth

-- | Generate a width @≥ 3@. Geometric strides are only defined for @w ≥ 3@.
genWidth :: Gen SomeWidth
genWidth =
  do sz <- getSize
     x <- chooseInt (3, sz + 6)
     mkSW x

-- | Like 'genWidth' but capped at 8, for tests that enumerate the
-- concretization.
genWidthSmall :: Gen SomeWidth
genWidthSmall = chooseInt (3, 8) >>= mkSW

mkSW :: Int -> Gen SomeWidth
mkSW x =
  case someNat (fromIntegral x :: Natural) of
    Just (Some n)
      | Just LeqProof <- isPosNat n
      , Just LeqProof <- testLeq (knownNat @3) n -> pure (SW n)
    _ -> error "test panic! GeoStrides.mkSW"

genNatBV :: NatRepr w -> Gen Natural
genNatBV w = fromInteger <$> chooseInteger (0, maxUnsigned w)

-- | An arbitrary nonnegative natural (for the number-theory helpers, which take
-- a width exponent and a value directly).
genNat :: Gen Natural
genNat = fromInteger <$> chooseInteger (0, 2 ^ (64 :: Int))

-- | A width exponent in @[3, sz + 6]@.
genWidthExp :: Gen Int
genWidthExp = do sz <- getSize; chooseInt (3, sz + 6)

tests :: TT.TestTree
tests = TT.testGroup "GeoStrides"
  [ -- 2-adic discrete log round-trips
    genTest "dlog5Pow5RoundTrip" $
      G.dlog5Pow5RoundTrip <$> genWidthExp <*> genNat
  , genTest "pow5Dlog5RoundTrip" $
      G.pow5Dlog5RoundTrip <$> genWidthExp <*> genNat
  , genTest "pow5Multiplicative" $
      G.pow5Multiplicative <$> genWidthExp <*> genNat <*> genNat
  , genTest "decomposeRecomposeRoundTrip" $
      G.decomposeRecomposeRoundTrip <$> genNat

    -- Queries
  , genTest "memberToList" $
      do SW n <- genWidthSmall
         G.memberToList n <$> G.genDomain n
  , genTest "toListMember" $
      do SW n <- genWidthSmall
         G.toListMember n <$> G.genDomain n <*> genNatBV n
  , genTest "toListNoDuplicates" $
      do SW n <- genWidthSmall
         G.toListNoDuplicates n <$> G.genDomain n
  , genTest "sizeViaToList" $
      do SW n <- genWidthSmall
         G.sizeViaToList n <$> G.genDomain n

    -- Arithmetic soundness
  , genTest "correct_neg" $
      do SW n <- genWidth
         G.correct_neg n <$> G.genDomain n <*> genNatBV n
  , genTest "correct_mul" $
      do SW n <- genWidth
         G.correct_mul n <$> G.genDomain n <*> genNatBV n <*> G.genDomain n <*> genNatBV n
  , genTest "correct_square" $
      do SW n <- genWidth
         G.correct_square n <$> G.genDomain n <*> genNatBV n
  , genTest "correct_pow" $
      do SW n <- genWidth
         G.correct_pow n <$> chooseInt (0, 10) <*> G.genDomain n <*> genNatBV n

    -- Lattice soundness and laws
  , genTest "correct_pseudoJoin" $
      do SW n <- genWidth
         G.correct_pseudoJoin n <$> G.genDomain n <*> genNatBV n <*> G.genDomain n <*> genNatBV n
  , genTest "correct_pseudoMeet" $
      do SW n <- genWidth
         G.correct_pseudoMeet n <$> G.genDomain n <*> G.genDomain n <*> genNatBV n
  , genTest "leqReflexive" $
      do SW n <- genWidth
         G.leqReflexive n <$> G.genDomain n
  , genTest "leqTransitive" $
      do SW n <- genWidth
         G.leqTransitive n <$> G.genDomain n <*> G.genDomain n <*> G.genDomain n
  , genTest "oddClassJoinAssoc" $
      G.oddClassJoinAssoc <$> genOddClass <*> genOddClass <*> genOddClass
  , genTest "oddClassMeetAssoc" $
      G.oddClassMeetAssoc <$> genOddClass <*> genOddClass <*> genOddClass
  ]

-- | Generate a random 'G.OddClass'.
genOddClass :: Gen G.OddClass
genOddClass = do
  j <- chooseInt (0, 2)
  pure ([G.OneMod4, G.ThreeMod4, G.OddClassTop] !! j)
