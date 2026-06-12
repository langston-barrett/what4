{-
Module      : Main
Copyright   : (c) Galois Inc, 2026
License     : BSD3

@strides-precision@: emit a CSV of strides-domain precision over the same
non-self-wrapping width-4 progressions that @sasi-precision@ uses, so the
two CSVs line up for direct comparison.

The op set, aggregator semantics, dedup logic, and CSV format match
@sasi-precision/main.cpp@; we drop the ops sasi can't run (udiv, urem,
sdiv, srem, pseudoMeet, pseudoJoin) so each row maps 1-1.

We mirror "PrecisionRegression.Common" for everything except the
enumeration (we filter to non-self-wrapping APs) and inline the helpers
to avoid pulling tasty into a plain executable.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import           Data.Bits ((.&.), shiftL, shiftR)
import qualified Data.Bits as Bits
import           Data.List (sort)
import qualified Data.Set as Set
import           Numeric.Natural (Natural)

import           Data.Parameterized.NatRepr (NatRepr, knownNat, maxUnsigned)

import qualified What4.Domains.BV.Strides as S

------------------------------------------------------------------------
-- Width 4 (mirrors PrecisionRegression.Common.w4 / mask4).

w4 :: NatRepr 4
w4 = knownNat @4

mask4 :: Natural
mask4 = fromInteger (maxUnsigned w4)

------------------------------------------------------------------------
-- Concrete oracle (mirrors PrecisionRegression.Common, lines 253-320).

cMask :: Natural -> Natural
cMask x = x .&. mask4

cAdd, cSub, cMul, cAnd, cOr, cXor :: Natural -> Natural -> Natural
cAdd x y = cMask (x + y)
cSub x y = cMask (x + (mask4 + 1 - y))
cMul x y = cMask (x * y)
cAnd x y = x .&. y
cOr  x y = x Bits..|. y
cXor x y = x `Bits.xor` y

cNegate, cNot :: Natural -> Natural
cNegate x = cMask (mask4 + 1 - x)
cNot   x = mask4 `Bits.xor` x

toSigned4 :: Natural -> Integer
toSigned4 x
  | x .&. 8 == 0 = toInteger x
  | otherwise    = toInteger x - 16

fromSigned4 :: Integer -> Natural
fromSigned4 x = fromInteger (x .&. toInteger mask4)

cShl, cLshr, cAshr :: Natural -> Natural -> Natural
cShl x y =
  let s = fromIntegral y :: Int
  in if s >= 4 then 0 else cMask (x `shiftL` s)
cLshr x y =
  let s = fromIntegral y :: Int
  in if s >= 4 then 0 else x `shiftR` s
cAshr x y =
  let s  = fromIntegral y :: Int
      sx = toSigned4 x
      s' = if s >= 4 then 3 else s
  in fromSigned4 (sx `shiftR` s')

------------------------------------------------------------------------
-- Enumeration: non-self-wrapping APs at width 4.
--
-- Mirrors @enumStrides4@ in "PrecisionRegression.Common", with the
-- additional guard @start + stride*i < 2^w@. Self-wrapping APs (whose
-- value-set crosses the south pole) are dropped because sasi's transfer
-- functions return unsound results on them.

enumNonWrapping4 :: [S.Domain 4]
enumNonWrapping4 =
  [ S.mk w4 start stride i
  | stride <- [1 .. mask4]
  , let g = stride .&. ((mask4 + 1) - stride)
  , let orbit = (mask4 + 1) `div` g
  , start <- [0 .. mask4]
  , i <- [0 .. orbit - 1]
  , start + stride * i < mask4 + 1
  ]

dedup :: (a -> [Natural]) -> [a] -> [a]
dedup toL = go Set.empty
  where
    go _ [] = []
    go seen (x : xs)
      | Set.member k seen = go seen xs
      | otherwise         = x : go (Set.insert k seen) xs
      where k = sort (toL x)

reps :: [S.Domain 4]
reps = dedup S.toList enumNonWrapping4

------------------------------------------------------------------------
-- Aggregators: same shape as PrecisionRegression.Common, inlined.

data Result = Result { resOp :: !String, resAbs :: !Integer, resConc :: !Integer }

leqRes :: String -> (S.Domain 4 -> S.Domain 4 -> Bool) -> Result
leqRes name op = Result name absTot concTot
  where
    pairs = [(a, b) | a <- reps, b <- reps]
    absTot = sum
      [ 1
      | (a, b) <- pairs
      , let bSet = Set.fromList (S.toList b)
      , all (`Set.member` bSet) (S.toList a)
      ]
    concTot = sum [ 1 | (a, b) <- pairs, op a b ]

unaryRes :: String -> (S.Domain 4 -> S.Domain 4) -> (Natural -> Natural) -> Result
unaryRes name absOp concOp = Result name absTot concTot
  where
    absTot  = sum [ fromIntegral (length (S.toList (absOp a))) | a <- reps ]
    concTot = sum [ fromIntegral (Set.size (Set.fromList (map concOp (S.toList a))))
                  | a <- reps ]

binaryRes :: String
          -> (S.Domain 4 -> S.Domain 4 -> S.Domain 4)
          -> (Natural -> Natural -> Natural)
          -> Result
binaryRes name absOp concOp = Result name absTot concTot
  where
    absTot = sum
      [ fromIntegral (length (S.toList (absOp a b))) | a <- reps, b <- reps ]
    concTot = sum
      [ fromIntegral (Set.size (Set.fromList [ concOp x y | x <- S.toList a, y <- S.toList b ]))
      | a <- reps, b <- reps
      ]

------------------------------------------------------------------------
-- CSV rendering. Same 1-decimal-place rounding as
-- @PrecisionRegression.Common.formatPercent@ so the output matches the
-- C++ side byte-for-byte.

formatPercent :: Integer -> Integer -> String
formatPercent num denom
  | denom == 0 = "0.0%"
  | otherwise =
      let perMille = (num * 1000) `div` denom
          (whole, frac) = perMille `divMod` 10
      in show whole ++ "." ++ show frac ++ "%"

formatRow :: Result -> String
formatRow r =
  resOp r ++ "," ++ show (resAbs r) ++ "," ++ show (resConc r) ++ ","
    ++ formatPercent (resConc r) (resAbs r)

main :: IO ()
main = do
  putStrLn "op,abs,conc,precision"
  mapM_ (putStrLn . formatRow) results
  where
    results =
      [ leqRes "leq" S.leq
      , unaryRes  "negate" (S.negate w4) cNegate
      , binaryRes "add"    (S.add w4) cAdd
      , binaryRes "sub"    (S.sub w4) cSub
      , binaryRes "mul"    (S.mul w4) cMul
      , unaryRes  "not"    (S.not w4) cNot
      , binaryRes "and"    (S.and w4) cAnd
      , binaryRes "or"     (S.or  w4) cOr
      , binaryRes "xor"    (S.xor w4) cXor
      , binaryRes "shl"    (S.shl  w4) cShl
      , binaryRes "lshr"   (S.lshr w4) cLshr
      , binaryRes "ashr"   (S.ashr w4) cAshr
      ]
