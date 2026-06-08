{-|
Module      : What4.Domains.BV.CLP
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Circular linear progressions (CLPs) following /Executable Analysis using
Abstract Interpretation with Circular Linear Progressions/ (Sen and Srikant,
MEMOCODE 2007).

This module intentionally implements only the core CLP representation together
with set union, addition, and the circularity/overflow handling needed for
addition.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module What4.Domains.BV.CLP
  ( Domain(..)
  , proper
  , bvdMask
  , member
  , size
    -- * Constructors
  , top
  , any
  , bottom
  , isBottom
  , singleton
  , clp
    -- * Operations
  , union
  , add
    -- * Correctness properties
  , genDomain
  , genElement
  , genPair
  , proper_generated
  , correct_union
  , correct_add
  ) where

import           Data.Bits
import           Data.Parameterized.NatRepr
import           GHC.TypeNats

import           Prelude hiding (any)

import           What4.Domains.Verification (Property, property, Gen, chooseInteger, chooseInt)

--------------------------------------------------------------------------------
-- Domain definition

-- | A CLP domain value of width @w@.
data Domain (w :: Nat)
  = BVDBottom !Integer
  | BVDTop !Integer
  | BVDCLP !Integer !Integer !Integer !Integer
  -- ^ Cached mask, lower bound, upper bound, stride.
  deriving (Eq, Ord, Show)

data RawCLP = RawCLP !Integer !Integer !Integer

--------------------------------------------------------------------------------
-- Basic queries

bvdMask :: Domain w -> Integer
bvdMask d =
  case d of
    BVDBottom mask -> mask
    BVDTop mask -> mask
    BVDCLP mask _ _ _ -> mask

proper :: forall w. (1 <= w) => NatRepr w -> Domain w -> Bool
proper w d =
  case d of
    BVDBottom mask -> mask == maxUnsigned w
    BVDTop mask -> mask == maxUnsigned w
    BVDCLP mask l u delta ->
      mask == maxUnsigned w
      && representable w l
      && representable w u
      && 0 <= delta
      && delta <= mask
      && if delta == 0
           then l == u
           else case stepsBetween w l u delta of
                  Just _ -> True
                  Nothing -> False

member :: forall w. (1 <= w) => NatRepr w -> Domain w -> Integer -> Bool
member w d x =
  case d of
    BVDBottom _ -> False
    BVDTop _ -> True
    BVDCLP _ l u delta ->
      if delta == 0 then canonicalSigned w x == l else
      case (stepsBetween w l (canonicalSigned w x) delta, stepsBetween w l u delta) of
        (Just i, Just n) -> i <= n
        _ -> False

size :: forall w. (1 <= w) => NatRepr w -> Domain w -> Integer
size w d =
  case d of
    BVDBottom _ -> 0
    BVDTop _ -> modulus w
    BVDCLP _ l u delta ->
      case stepsBetween w l u delta of
        Just n -> n + 1
        Nothing -> 0

--------------------------------------------------------------------------------
-- Constructors

top :: NatRepr w -> Domain w
top w = BVDTop (maxUnsigned w)

any :: NatRepr w -> Domain w
any = top

bottom :: NatRepr w -> Domain w
bottom w = BVDBottom (maxUnsigned w)

isBottom :: Domain w -> Bool
isBottom d =
  case d of
    BVDBottom _ -> True
    _ -> False

singleton :: forall w. (1 <= w) => NatRepr w -> Integer -> Domain w
singleton w x =
  let y = canonicalSigned w x in
  BVDCLP (maxUnsigned w) y y 0

clp :: forall w. (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Domain w
clp w l u delta
  | delta == 0 = singleton w l
  | otherwise =
      BVDCLP (maxUnsigned w) (canonicalSigned w l) (canonicalSigned w u) (delta .&. maxUnsigned w)

--------------------------------------------------------------------------------
-- Set operations

union :: forall w. (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
union w x0 y0 =
  let x = normalizeDomain w x0
      y = normalizeDomain w y0
  in
  case (x, y) of
    (BVDBottom _, _) -> y
    (_, BVDBottom _) -> x
    (BVDTop _, _) -> x
    (_, BVDTop _) -> y
    (BVDCLP {}, BVDCLP {})
      | isSingleArcCLP w x && isSingleArcCLP w y ->
          endpointUnion w x y
      | otherwise -> top w

endpointUnion :: forall w. (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
endpointUnion w (BVDCLP _ l1 u1 d1) (BVDCLP _ l2 u2 d2) =
  case filter (validCandidate . candidateDomain) candidates of
    [] -> top w
    cs ->
      candidateDomain (minimumBySpan cs)
  where
    endpoints = [l1, u1, l2, u2]

    candidates =
      [ Candidate a b diff score' $
          normalizeDomain w (BVDCLP (maxUnsigned w) a b delta)
      | a <- endpoints
      , b <- endpoints
      , let diff = clpDistance w a b
      , let delta = if diff == 0 then 0 else gcdMany [diff, d1, d2]
      , let score' = if delta == 0 then 0 else diff `div` delta
      ]

    validCandidate cand = subsetDomain w cand (BVDCLP (maxUnsigned w) l1 u1 d1)
                       && subsetDomain w cand (BVDCLP (maxUnsigned w) l2 u2 d2)
endpointUnion _ _ _ = error "endpointUnion: expected concrete CLP values"

data Candidate w = Candidate
  { candidateLower :: !Integer
  , candidateUpper :: !Integer
  , candidateDiff :: !Integer
  , candidateScore :: !Integer
  , candidateDomain :: !(Domain w)
  }

minimumBySpan :: [Candidate w] -> Candidate w
minimumBySpan = foldr1 pick
  where
    pick x y
      | candidateScore x < candidateScore y = x
      | candidateScore y < candidateScore x = y
      | candidateDiff x <= candidateDiff y = x
      | otherwise = y

subsetDomain :: forall w. (1 <= w) => NatRepr w -> Domain w -> Domain w -> Bool
subsetDomain _ (BVDTop _) _ = True
subsetDomain _ _ (BVDBottom _) = True
subsetDomain w outer@(BVDCLP _ a b d) inner@(BVDCLP _ l u delta) =
  case (d, delta) of
    (0, 0) -> member w outer l
    (0, _) -> False
    (_, 0) -> member w outer l
    _ ->
      delta `mod` d == 0
      && member w outer l
      && member w outer u
      && case (stepsBetween w a l d, stepsBetween w a b d, stepsBetween w l u delta) of
           (Just startIx, Just outerSteps, Just innerSteps) ->
             startIx + innerSteps * (delta `div` d) <= outerSteps
           _ -> False
subsetDomain _ _ _ = False

--------------------------------------------------------------------------------
-- Addition

add :: forall w. (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
add w x0 y0 =
  let x = normalizeDomain w x0
      y = normalizeDomain w y0
  in
  case (x, y) of
    (BVDBottom _, _) -> x
    (_, BVDBottom _) -> y
    (BVDTop _, _) -> top w
    (_, BVDTop _) -> top w
    _
      | not (isSingleArcCLP w x && isSingleArcCLP w y) -> top w
    _ ->
      foldr (union w) (bottom w)
        [ normalizeDomain w (reduceOverflow w (rawAdd a b))
        | a <- splitCircular w x
        , b <- splitCircular w y
        ]

--------------------------------------------------------------------------------
-- Correctness properties

genDomain :: forall w. (1 <= w) => NatRepr w -> Gen (Domain w)
genDomain w = do
  tag <- chooseInt (0, 5)
  case tag of
    0 -> pure (bottom w)
    1 -> pure (top w)
    _ -> do
      -- IMPORTANT: Hedgehog builds shrink trees that are quadratic or worse
      -- in the size of integer ranges. Even with width 8 (range 0-255),
      -- uncapped ranges cause 40+GB allocations for 10 tests.
      -- We must cap ALL integer ranges to small values.
      startU <- chooseInteger (0, min 64 (maxUnsigned w))
      delta <- chooseInteger (0, min 64 (maxUnsigned w))
      if delta == 0 then
        pure (singleton w startU)
      else do
        let orbitLen = modulus w `div` gcd delta (modulus w)
        let cappedOrbitLen = min 4 orbitLen
        n <- chooseInteger (0, cappedOrbitLen - 1)
        pure (mkProgression w startU delta n)

genElement :: forall w. (1 <= w) => Domain w -> Gen Integer
genElement d =
  case d of
    BVDBottom _ -> error "genElement: empty domain"
    BVDTop mask -> chooseInteger (0, mask)
    BVDCLP _ l u delta ->
      case stepsBetweenFromMask (bvdMask d) l u delta of
        Nothing -> error "genElement: malformed CLP"
        Just n -> do
          i <- chooseInteger (0, n)
          pure (clpStepFromMask (bvdMask d) l delta i)

genPair :: forall w. (1 <= w) => NatRepr w -> Gen (Domain w, Integer)
genPair w = do
  d <- genNonBottomDomain w
  x <- genElement d
  pure (d, x)

proper_generated :: forall w. (1 <= w) => NatRepr w -> Domain w -> Property
proper_generated w d = property (proper w d)

correct_union :: forall w. (1 <= w) => NatRepr w -> (Domain w, Integer) -> (Domain w, Integer) -> Property
correct_union w (a, x) (b, y) =
  let ab = union w a b in
  property (member w ab x && member w ab y)

correct_add :: forall w. (1 <= w) => NatRepr w -> (Domain w, Integer) -> (Domain w, Integer) -> Property
correct_add w (a, x) (b, y) =
  property (member w (add w a b) (canonicalSigned w (x + y)))

rawAdd :: Domain w -> Domain w -> RawCLP
rawAdd (BVDCLP _ l1 u1 d1) (BVDCLP _ l2 u2 d2) =
  RawCLP (l1 + l2) (u1 + u2) (gcd d1 d2)
rawAdd _ _ = error "rawAdd: expected concrete CLP values"

reduceOverflow :: forall w. (1 <= w) => NatRepr w -> RawCLP -> Domain w
reduceOverflow w (RawCLP l u delta)
  | delta == 0 = singleton w l
  | representable w l && representable w u =
      BVDCLP (maxUnsigned w) l u delta
  | l > u =
      top w
  | representable w l =
      let pUpper = l + delta * ((signedMax w - l) `div` delta)
          p = BVDCLP (maxUnsigned w) l pUpper delta
          first = pUpper + delta
      in union w p (reduceOverflowTail w first u delta)
  | representable w u =
      let pLower = u - delta * ((u - signedMin w) `div` delta)
          p = BVDCLP (maxUnsigned w) pLower u delta
          lastBefore = pLower - delta
      in union w p (reduceOverflowHead w l lastBefore delta)
  | otherwise =
      approximateOverflow w l delta

reduceOverflowTail :: forall w. (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Domain w
reduceOverflowTail w first u delta =
  let shiftedLower = first - modulus w
      shiftedUpper = u - modulus w
  in if representable w shiftedLower && representable w shiftedUpper
       then BVDCLP (maxUnsigned w) shiftedLower shiftedUpper delta
       else approximateOverflow w first delta

reduceOverflowHead :: forall w. (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Domain w
reduceOverflowHead w l lastBefore delta =
  let shiftedLower = l + modulus w
      shiftedUpper = lastBefore + modulus w
  in if representable w shiftedLower && representable w shiftedUpper
       then BVDCLP (maxUnsigned w) shiftedLower shiftedUpper delta
       else approximateOverflow w l delta

approximateOverflow :: forall w. (1 <= w) => NatRepr w -> Integer -> Integer -> Domain w
approximateOverflow w x delta =
  let alpha = trailingZeros delta
      delta' = bit alpha
      t = (canonicalUnsigned w x) .&. (delta' - 1)
      upper = t + delta' * ((maxUnsigned w - t) `div` delta')
  in BVDCLP (maxUnsigned w) (unsignedToSigned w t) (unsignedToSigned w upper) delta'

--------------------------------------------------------------------------------
-- Circularity handling

splitCircular :: forall w. (1 <= w) => NatRepr w -> Domain w -> [Domain w]
splitCircular w d =
  case d of
    BVDBottom _ -> []
    BVDTop _ -> [d]
    BVDCLP _ l u delta
      | delta == 0 -> [d]
      | l <= u -> [d]
      | otherwise ->
          let pUpper = l + delta * ((signedMax w - l) `div` delta)
              qLower = u - delta * ((u - signedMin w) `div` delta)
          in [ BVDCLP (maxUnsigned w) l pUpper delta
             , BVDCLP (maxUnsigned w) qLower u delta
             ]

normalizeDomain :: forall w. (1 <= w) => NatRepr w -> Domain w -> Domain w
normalizeDomain w d =
  case d of
    BVDCLP _ l u delta
      | l == u -> singleton w l
      | delta == 1 && clpDistance w l u + 1 == modulus w -> top w
      | otherwise -> d
    _ -> d

-- | Whether a domain value satisfies the single-arc CLP side condition:
-- stepping from @l@ by @delta@ reaches @u@ exactly at the circular distance.
isSingleArcCLP :: forall w. (1 <= w) => NatRepr w -> Domain w -> Bool
isSingleArcCLP w d =
  case d of
    BVDBottom _ -> True
    BVDTop _ -> True
    BVDCLP _ l u delta
      | delta == 0 -> True
      | otherwise ->
          case stepsBetween w l u delta of
            Just n -> n * delta == clpDistance w l u
            Nothing -> False

--------------------------------------------------------------------------------
-- Helpers

genNonBottomDomain :: forall w. (1 <= w) => NatRepr w -> Gen (Domain w)
genNonBottomDomain w =
  -- Avoid recursion which causes Hedgehog to build huge shrink trees.
  -- Use explicit retry loop instead.
  let go = do
        d <- genDomain w
        if isBottom d then go else pure d
  in go

mkProgression :: forall w. (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Domain w
mkProgression w startU delta n =
  let l = unsignedToSigned w startU
      u = unsignedToSigned w ((startU + n * delta) .&. maxUnsigned w)
  in BVDCLP (maxUnsigned w) l u delta

modulus :: NatRepr w -> Integer
modulus w = maxUnsigned w + 1

signedMin :: (1 <= w) => NatRepr w -> Integer
signedMin w = negate (bit (widthVal w - 1))

signedMax :: (1 <= w) => NatRepr w -> Integer
signedMax w = bit (widthVal w - 1) - 1

representable :: (1 <= w) => NatRepr w -> Integer -> Bool
representable w x = signedMin w <= x && x <= signedMax w

canonicalUnsigned :: forall w. NatRepr w -> Integer -> Integer
canonicalUnsigned w x = x .&. maxUnsigned w

unsignedToSigned :: forall w. (1 <= w) => NatRepr w -> Integer -> Integer
unsignedToSigned w x =
  let y = x .&. maxUnsigned w
  in if testBit y (widthVal w - 1)
       then y - modulus w
       else y

canonicalSigned :: forall w. (1 <= w) => NatRepr w -> Integer -> Integer
canonicalSigned w = unsignedToSigned w . canonicalUnsigned w

clpDistance :: forall w. (1 <= w) => NatRepr w -> Integer -> Integer -> Integer
clpDistance w l u
  | l <= u = u - l
  | otherwise = (signedMax w - l) + 1 + (u - signedMin w)

gcdMany :: [Integer] -> Integer
gcdMany = foldr gcd 0

trailingZeros :: Integer -> Int
trailingZeros n
  | n <= 0 = error "trailingZeros: expected positive integer"
  | otherwise = go 0 n
  where
    go k m
      | odd m = k
      | otherwise = go (k + 1) (m `div` 2)

stepsBetween :: forall w. (1 <= w) => NatRepr w -> Integer -> Integer -> Integer -> Maybe Integer
stepsBetween w l u delta
  = stepsBetweenFromMask (maxUnsigned w) l u delta

stepsBetweenFromMask :: Integer -> Integer -> Integer -> Integer -> Maybe Integer
stepsBetweenFromMask mask l u delta
  | delta == 0 = if l == u then Just 0 else Nothing
  | otherwise =
      let m = mask + 1
          diff = ((u .&. mask) - (l .&. mask)) `mod` m
          g = gcd delta m
      in if diff `mod` g /= 0
           then Nothing
           else do
             inv <- modInverse (delta `div` g) (m `div` g)
             pure (((diff `div` g) * inv) `mod` (m `div` g))

clpStepFromMask :: Integer -> Integer -> Integer -> Integer -> Integer
clpStepFromMask mask l delta i =
  let m = mask + 1
      u = ((l .&. mask) + i * delta) `mod` m
      signBit = m `div` 2
  in if u .&. signBit /= 0 then u - m else u

modInverse :: Integer -> Integer -> Maybe Integer
modInverse a m =
  let (g, x, _) = egcd a m in
  if g == 1 then Just (x `mod` m) else Nothing

egcd :: Integer -> Integer -> (Integer, Integer, Integer)
egcd a b
  | b == 0 = (a, 1, 0)
  | otherwise =
      let (g, s, t) = egcd b (a `mod` b)
      in (g, t, s - (a `div` b) * t)
