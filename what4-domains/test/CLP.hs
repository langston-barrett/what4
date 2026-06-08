{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module CLP (tests) where

import           Control.Monad (forM_, unless)
import           Data.Bits
import           Data.List (nub)
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as HU

import           Data.Parameterized.NatRepr (NatRepr, intValue, isPosNat, LeqProof(..), someNat)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.CLP as C
import           What4.Domains.Verification (Gen, chooseInt, getSize)
import           VerifyBindings (genTest)

data SomeWidth where
  SW :: (1 <= w) => NatRepr w -> SomeWidth

genWidth :: Gen SomeWidth
genWidth = do
  sz <- getSize
  -- Cap at width 8 to avoid expensive modular arithmetic in stepsBetween/union.
  -- Widths beyond 8 can create CLPs with orbit lengths of 2^w or more, making
  -- stepsBetween's modular inverse computations prohibitively expensive.
  x <- chooseInt (1, min 8 (sz + 4))
  case someNat (fromIntegral x :: Natural) of
    Just (Some n)
      | Just LeqProof <- isPosNat n -> pure (SW n)
    _ -> error "test panic! genWidth"

tests :: TT.TestTree
tests = TT.testGroup "CLP"
  [ genTest "proper_generated" $
      do SW n <- genWidth
         C.proper_generated n <$> C.genDomain n
  , genTest "correct_union" $
      do SW n <- genWidth
         C.correct_union n <$> C.genPair n <*> C.genPair n
  , genTest "correct_add" $
      do SW n <- genWidth
         C.correct_add n <$> C.genPair n <*> C.genPair n
  , reportExampleTests
  , TT.testGroup "exhaustive"
      [ exhaustiveCase "union_sound" checkUnionSound
      , exhaustiveCase "add_sound" checkAddSound
      ]
  ]

reportExampleTests :: TT.TestTree
reportExampleTests =
  case someNat (4 :: Natural) of
    Just (Some w)
      | Just LeqProof <- isPosNat w ->
          TT.testGroup "report examples"
            [ HU.testCase "{1, 2^n-1} joins to CLP(MAXD, 1, 2)" $ do
                let one = C.singleton w 1
                    maxD = C.singleton w (-1)
                    want = C.clp w (-1) 1 2
                HU.assertEqual "report §3 circularity example 1" want (C.union w one maxD)
            , HU.testCase "{-2^(n-1), 2^(n-1)-1} joins to CLP(MAXP, MAXN, 1)" $ do
                let maxP = C.singleton w 7
                    maxN = C.singleton w (-8)
                    want = C.clp w 7 (-8) 1
                HU.assertEqual "report §3 circularity example 2" want (C.union w maxP maxN)
            ]
    _ -> error "test panic! reportExampleTests"

exhaustiveCase :: String -> (forall w. (1 <= w) => NatRepr w -> HU.Assertion) -> TT.TestTree
exhaustiveCase label assertion =
  -- Cap at width 3 to avoid OOM. Width 4 generates ~4096 domains; the nested
  -- loops in checkAddSound create ~4096² × 16² ≈ 1B iterations.
  TT.testGroup label (map mkCase ([1 .. 3] :: [Natural]))
  where
    mkCase n =
      case someNat n of
        Just (Some w)
          | Just LeqProof <- isPosNat w ->
              HU.testCase ("w=" ++ show n) (assertion w)
        _ -> error "test panic! exhaustiveCase"

checkUnionSound :: forall w. (1 <= w) => NatRepr w -> HU.Assertion
checkUnionSound w = do
  let ds = exhaustiveDomains w
  forM_ ds $ \x ->
    forM_ ds $ \y -> do
      let z = C.union w x y
      forM_ (elementsOf w x) $ \v ->
        unless (C.member w z v) $
          HU.assertFailure (context w x y ++ "\nmissing lhs element " ++ show v)
      forM_ (elementsOf w y) $ \v ->
        unless (C.member w z v) $
          HU.assertFailure (context w x y ++ "\nmissing rhs element " ++ show v)

checkAddSound :: forall w. (1 <= w) => NatRepr w -> HU.Assertion
checkAddSound w = do
  let ds = exhaustiveDomains w
  forM_ ds $ \x ->
    forM_ ds $ \y -> do
      let z = C.add w x y
      forM_ (elementsOf w x) $ \vx ->
        forM_ (elementsOf w y) $ \vy -> do
          let sumXY = canonicalSigned w (vx + vy)
          unless (C.member w z sumXY) $
            HU.assertFailure
              (context w x y ++ "\nmissing sum " ++ show sumXY ++ " from " ++ show (vx, vy))

context :: forall w. (1 <= w) => NatRepr w -> C.Domain w -> C.Domain w -> String
context w x y =
  "width=" ++ show (intValue w) ++ ", x=" ++ show x ++ ", y=" ++ show y

exhaustiveDomains :: forall w. (1 <= w) => NatRepr w -> [C.Domain w]
exhaustiveDomains w =
  nub $
    map (normalizeModel w) $
      C.bottom w : C.top w :
        [ C.BVDCLP (mask w) l u delta
        | l <- signedValues w
        , u <- signedValues w
        , delta <- [0 .. mask w]
        , isSingleArcShape w l u delta
        ]

isSingleArcShape :: forall w. (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Bool
isSingleArcShape w l u delta
  | delta == 0 = l == u
  | otherwise =
      case reachSteps w l u delta of
        Just n -> n * delta == circularDistance w l u
        Nothing -> False

reachSteps :: forall w. (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Maybe Integer
reachSteps w l u delta = go 0 (canonicalSigned w l)
  where
    limit = modulus w

    go i cur
      | cur == canonicalSigned w u = Just i
      | i >= limit = Nothing
      | otherwise = go (i + 1) (canonicalSigned w (cur + delta))

elementsOf :: forall w. (1 <= w) => NatRepr w -> C.Domain w -> [Integer]
elementsOf w d = filter (C.member w d) (signedValues w)

normalizeModel :: forall w. (1 <= w) => NatRepr w -> C.Domain w -> C.Domain w
normalizeModel w d =
  case d of
    C.BVDCLP _ l u delta
      | l == u -> C.singleton w l
      | delta == 1 && circularDistance w l u + 1 == modulus w -> C.top w
      | otherwise -> C.BVDCLP (mask w) l u delta
    _ -> d

mask :: NatRepr w -> Integer
mask w = bit (fromInteger (intValue w)) - 1

modulus :: NatRepr w -> Integer
modulus w = mask w + 1

signedMin :: NatRepr w -> Integer
signedMin w = negate (bit (fromInteger (intValue w) - 1))

signedMax :: NatRepr w -> Integer
signedMax w = bit (fromInteger (intValue w) - 1) - 1

signedValues :: NatRepr w -> [Integer]
signedValues w = map (unsignedToSigned w) [0 .. mask w]

canonicalUnsigned :: NatRepr w -> Integer -> Integer
canonicalUnsigned w x = x .&. mask w

unsignedToSigned :: NatRepr w -> Integer -> Integer
unsignedToSigned w x =
  let y = x .&. mask w
  in if testBit y (fromInteger (intValue w) - 1)
       then y - modulus w
       else y

canonicalSigned :: NatRepr w -> Integer -> Integer
canonicalSigned w = unsignedToSigned w . canonicalUnsigned w

circularDistance :: NatRepr w -> Integer -> Integer -> Integer
circularDistance w l u
  | l <= u = u - l
  | otherwise = (signedMax w - l) + 1 + (u - signedMin w)
