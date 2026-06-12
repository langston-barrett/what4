{-
Module      : PrecisionRegression.Common
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Shared infrastructure for the precision regression test:

  * Width-4 enumeration scaffolding ('DomainEnum', 'dedup', 'enumStrides4').
  * Concrete-value-set operations on @Natural@ at width 4 (the oracle that
    each abstract op is compared against).
  * Aggregator helpers ('unaryResult', 'binaryResult',
    'binaryResultFiltered', 'scaleResult', 'latticeResult') that turn an
    abstract op + a concrete op into a precision 'Result'.
  * CSV rendering and the per-domain compare/update driver ('domainTests').
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module PrecisionRegression.Common
  ( -- * Width-4 enumeration
    w4
  , mask4
  , DomainEnum(..)
  , dedup
  , enumStrides4
    -- * Aggregator
  , Result(..)
  , unaryResult
  , binaryResult
  , binaryResultFiltered
  , scaleResult
  , latticeResult
  , latticeMaybeResult
  , latticeUnderApproxMaybeResult
  , leqResult
    -- * Concrete operations
  , cAdd, cSub, cMul, cAnd, cOr, cXor
  , cNegate, cNot, cScale
  , cUdivPartial, cUremPartial, cSdivPartial, cSremPartial
  , cUdivSmtlib, cUremSmtlib, cSdivSmtlib, cSremSmtlib
  , cShl, cLshr, cAshr, cRol, cRor
  , cJoin, cMeet
  , cAssumeUlt, cAssumeUle, cAssumeUgt, cAssumeUge
  , cAssumeSlt, cAssumeSle, cAssumeSgt, cAssumeSge
    -- * Driver
  , domainTests
  ) where

import           Data.Bits ((.&.), shiftL, shiftR)
import qualified Data.Bits as Bits
import           Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import           Numeric.Natural (Natural)

import           Data.Parameterized.NatRepr (NatRepr, knownNat, maxUnsigned)

import qualified What4.Domains.BV.Strides as S

import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.HUnit (testCase, (@?=))

------------------------------------------------------------------------
-- Width 4

w4 :: NatRepr 4
w4 = knownNat @4

mask4 :: Natural
mask4 = fromInteger (maxUnsigned w4)

------------------------------------------------------------------------
-- Enumerating representatives of a domain at width 4

-- | All distinguishable abstract elements of a domain at width 4, plus the
-- 'toList' projection used to compare value-sets.
data DomainEnum a = DomainEnum
  { deReps   :: ![a]
  , deToList :: !(a -> [Natural])
  }

dedup :: (a -> [Natural]) -> [a] -> [a]
dedup toL = go Set.empty
  where
    go _ [] = []
    go seen (x : xs)
      | Set.member k seen = go seen xs
      | otherwise         = x : go (Set.insert k seen) xs
      where k = sort (toL x)

-- | Enumerate every proper 'S.Domain' at width 4. Reused as the building
-- block for both the Strides and StridedInterval enumerations.
enumStrides4 :: [S.Domain 4]
enumStrides4 =
  [ S.mk w4 start stride i
  | stride <- [1 .. mask4]
  , let g = stride .&. ((mask4 + 1) - stride)
  , let orbit = (mask4 + 1) `div` g
  , start <- [0 .. mask4]
  , i <- [0 .. orbit - 1]
  ]

------------------------------------------------------------------------
-- Aggregation

data Result = Result
  { resOp   :: !String
  , resAbs  :: !Integer
  , resConc :: !Integer
  }

unaryResult ::
  DomainEnum a ->
  String -> (a -> a) -> (Natural -> Natural) -> Result
unaryResult de name absOp concOp = Result name absTot concTot
  where
    reps = deReps de
    toL  = deToList de
    absTot  = sum [ fromIntegral (length (toL (absOp a))) | a <- reps ]
    concTot =
      sum [ fromIntegral (Set.size (Set.fromList (map concOp (toL a))))
          | a <- reps
          ]

binaryResultFiltered ::
  DomainEnum a ->
  String ->
  (a -> a -> a) ->
  (Natural -> Natural -> Maybe Natural) ->
  Result
binaryResultFiltered de name absOp concOp = Result name absTot concTot
  where
    reps = deReps de
    toL  = deToList de
    absTot =
      sum [ fromIntegral (length (toL (absOp a b))) | a <- reps, b <- reps ]
    concTot =
      sum [ fromIntegral (Set.size (Set.fromList
              [ z | x <- toL a, y <- toL b
                  , Just z <- [concOp x y] ]))
          | a <- reps, b <- reps
          ]

binaryResult ::
  DomainEnum a ->
  String ->
  (a -> a -> a) ->
  (Natural -> Natural -> Natural) ->
  Result
binaryResult de name absOp concOp =
  binaryResultFiltered de name absOp (\x y -> Just (concOp x y))

-- | 'scale' takes an Integer constant; aggregate over @k in [0, mask4]@.
scaleResult :: DomainEnum a -> (Integer -> a -> a) -> Result
scaleResult de absOp = Result "scale" absTot concTot
  where
    reps = deReps de
    toL  = deToList de
    absTot  = sum [ fromIntegral (length (toL (absOp (toInteger k) a)))
                  | k <- [0 .. mask4], a <- reps ]
    concTot = sum [ fromIntegral (Set.size (Set.fromList
                      [ cScale k x | x <- toL a ]))
                  | k <- [0 .. mask4], a <- reps ]

-- | Aggregator for a sound (one-way) partial order @leq a b ==> toList a ⊆
-- toList b@. @abs@ counts pairs satisfying semantic containment (the ideal
-- ceiling); @conc@ counts pairs the syntactic check actually returns 'True'
-- for. The ratio is the check's recall.
leqResult :: DomainEnum a -> String -> (a -> a -> Bool) -> Result
leqResult de name absOp = Result name absTot concTot
  where
    reps = deReps de
    toL  = deToList de
    pairs = [ (a, b) | a <- reps, b <- reps ]
    absTot = sum
      [ 1
      | (a, b) <- pairs
      , let bSet = Set.fromList (toL b)
      , all (`Set.member` bSet) (toL a)
      ]
    concTot = sum [ 1 | (a, b) <- pairs, absOp a b ]

-- | Aggregator for lattice operations whose oracle is a set operation on
-- the underlying value-sets, rather than a pointwise function.
latticeResult ::
  DomainEnum a ->
  String ->
  (a -> a -> a) ->
  ([Natural] -> [Natural] -> Set.Set Natural) ->
  Result
latticeResult de name absOp concOp = Result name absTot concTot
  where
    reps = deReps de
    toL  = deToList de
    absTot  = sum [ fromIntegral (length (toL (absOp a b)))
                  | a <- reps, b <- reps ]
    concTot = sum [ fromIntegral (Set.size (concOp (toL a) (toL b)))
                  | a <- reps, b <- reps ]

-- | Like 'latticeResult', but for lattice operations that return @Maybe a@ —
-- e.g., a 'meet' on a domain without a native bottom, where 'Nothing'
-- represents the empty intersection. 'Nothing' contributes 0 to the
-- abstract cardinality.
latticeMaybeResult ::
  DomainEnum a ->
  String ->
  (a -> a -> Maybe a) ->
  ([Natural] -> [Natural] -> Set.Set Natural) ->
  Result
latticeMaybeResult de name absOp concOp = Result name absTot concTot
  where
    reps = deReps de
    toL  = deToList de
    absTot  = sum [ fromIntegral (maybe 0 (length . toL) (absOp a b))
                  | a <- reps, b <- reps ]
    concTot = sum [ fromIntegral (Set.size (concOp (toL a) (toL b)))
                  | a <- reps, b <- reps ]

-- | Like 'latticeMaybeResult', but for /under/-approximating lattice ops:
-- the abstract result is contained in the true value, so the right precision
-- question is \"what fraction of the truth did we capture?\".
--
-- The CSV columns are inverted relative to the over-approx convention to
-- keep the @precision@ percentage in the @[0, 100]%@ range:
--
--   * @abs@   column holds the /true/ (concrete) cardinality (denominator).
--   * @conc@  column holds the /abstract/ cardinality (numerator).
--
-- That way @precision = conc \/ abs = |abstract| \/ |true|@, which is the
-- under-approx analogue of the over-approx @precision = |true| \/ |abstract|@.
-- 100% means exact; lower means more witnesses dropped.
latticeUnderApproxMaybeResult ::
  DomainEnum a ->
  String ->
  (a -> a -> Maybe a) ->
  ([Natural] -> [Natural] -> Set.Set Natural) ->
  Result
latticeUnderApproxMaybeResult de name absOp concOp = Result name trueTot absTot
  where
    reps = deReps de
    toL  = deToList de
    absTot  = sum [ fromIntegral (maybe 0 (length . toL) (absOp a b))
                  | a <- reps, b <- reps ]
    trueTot = sum [ fromIntegral (Set.size (concOp (toL a) (toL b)))
                  | a <- reps, b <- reps ]

------------------------------------------------------------------------
-- Concrete operations

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

cScale :: Natural -> Natural -> Natural
cScale k x = cMask (k * x)

toSigned4 :: Natural -> Integer
toSigned4 x
  | x .&. 8 == 0 = toInteger x
  | otherwise    = toInteger x - 16

fromSigned4 :: Integer -> Natural
fromSigned4 x = fromInteger (x .&. toInteger mask4)

cUdivPartial, cUremPartial, cSdivPartial, cSremPartial
  :: Natural -> Natural -> Maybe Natural
cUdivPartial _ 0 = Nothing
cUdivPartial x y = Just (x `div` y)
cUremPartial _ 0 = Nothing
cUremPartial x y = Just (x `mod` y)
cSdivPartial _ 0 = Nothing
cSdivPartial x y = Just (fromSigned4 (toSigned4 x `quot` toSigned4 y))
cSremPartial _ 0 = Nothing
cSremPartial x y = Just (fromSigned4 (toSigned4 x `rem` toSigned4 y))

cUdivSmtlib, cUremSmtlib, cSdivSmtlib, cSremSmtlib
  :: Natural -> Natural -> Natural
cUdivSmtlib _ 0 = mask4
cUdivSmtlib x y = x `div` y
cUremSmtlib x 0 = x
cUremSmtlib x y = x `mod` y
cSdivSmtlib x 0
  | toSigned4 x >= 0 = mask4   -- -1
  | otherwise        = 1
cSdivSmtlib x y = fromSigned4 (toSigned4 x `quot` toSigned4 y)
cSremSmtlib x 0 = x
cSremSmtlib x y = fromSigned4 (toSigned4 x `rem` toSigned4 y)

cShl, cLshr, cAshr, cRol, cRor :: Natural -> Natural -> Natural
cShl x y =
  let s = fromIntegral y :: Int
  in if s >= 4 then 0 else cMask (x `shiftL` s)
cLshr x y =
  let s = fromIntegral y :: Int
  in if s >= 4 then 0 else x `shiftR` s
cAshr x y =
  let s = fromIntegral y :: Int
      sx = toSigned4 x
      s' = if s >= 4 then 3 else s
  in fromSigned4 (sx `shiftR` s')
cRol x y =
  let s = fromIntegral (y `mod` 4) :: Int
  in cMask ((x `shiftL` s) Bits..|. (x `shiftR` (4 - s)))
cRor x y =
  let s = fromIntegral (y `mod` 4) :: Int
  in cMask ((x `shiftR` s) Bits..|. (x `shiftL` (4 - s)))

-- | Oracle for lattice 'join': set union of value-sets.
cJoin :: [Natural] -> [Natural] -> Set.Set Natural
cJoin xs ys = Set.fromList xs `Set.union` Set.fromList ys

-- | Oracle for lattice 'meet': set intersection of value-sets.
cMeet :: [Natural] -> [Natural] -> Set.Set Natural
cMeet xs ys = Set.fromList xs `Set.intersection` Set.fromList ys

-- | Oracle for @assumeOp a b@: @{ x ∈ γ(a) | ∃ y ∈ γ(b). x op y }@.
cAssumeBy :: (Natural -> Natural -> Bool) -> [Natural] -> [Natural] -> Set.Set Natural
cAssumeBy op xs ys = Set.fromList [ x | x <- xs, any (op x) ys ]

cAssumeUlt, cAssumeUle, cAssumeUgt, cAssumeUge,
 cAssumeSlt, cAssumeSle, cAssumeSgt, cAssumeSge ::
  [Natural] -> [Natural] -> Set.Set Natural
cAssumeUlt = cAssumeBy (<)
cAssumeUle = cAssumeBy (<=)
cAssumeUgt = cAssumeBy (>)
cAssumeUge = cAssumeBy (>=)
cAssumeSlt = cAssumeBy (\x y -> toSigned4 x <  toSigned4 y)
cAssumeSle = cAssumeBy (\x y -> toSigned4 x <= toSigned4 y)
cAssumeSgt = cAssumeBy (\x y -> toSigned4 x >  toSigned4 y)
cAssumeSge = cAssumeBy (\x y -> toSigned4 x >= toSigned4 y)

------------------------------------------------------------------------
-- CSV rendering

renderCsv :: [Result] -> Text
renderCsv rs = T.unlines (T.pack "op,abs,conc,precision" : map formatRow rs)

formatRow :: Result -> Text
formatRow r =
  T.intercalate (T.singleton ',')
    [ T.pack (resOp r)
    , T.pack (show (resAbs r))
    , T.pack (show (resConc r))
    , formatPercent (resConc r) (resAbs r)
    ]

-- | @num \/ denom@ as a percentage to 1 decimal place.
formatPercent :: Integer -> Integer -> Text
formatPercent num denom
  | denom == 0 = T.pack "0.0%"
  | otherwise =
      let perMille = (num * 1000) `div` denom
          (whole, frac) = perMille `divMod` 10
      in T.pack (show whole ++ "." ++ show frac ++ "%")

------------------------------------------------------------------------
-- CSV parsing

-- | Parse a CSV into a map from op name to (abs, conc) row.  The header
-- line and the precision column are ignored; only abs and conc are used
-- so that floating-point formatting differences never cause false misses.
parseCsv :: Text -> Map.Map Text (Integer, Integer)
parseCsv txt = Map.fromList
  [ (op, (read (T.unpack absT), read (T.unpack concT)))
  | line <- drop 1 (T.lines txt)
  , let cols = T.splitOn (T.singleton ',') line
  , [op, absT, concT, _prec] <- [cols]
  ]

------------------------------------------------------------------------
-- Driver

-- | Build a 'TestTree' for one domain.  In update mode the CSV is
-- rewritten and every test trivially passes; in normal mode each op
-- becomes one HUnit test that checks (abs, conc) against the stored row.
domainTests :: Bool -> String -> FilePath -> [Result] -> IO TestTree
domainTests update label path results =
  if update
    then do
      TIO.writeFile path (renderCsv results)
      putStrLn ("Wrote " ++ path)
      pure $ testGroup label
        [ testCase (resOp r) (pure ()) | r <- results ]
    else do
      csv <- TIO.readFile path
      let expected = parseCsv csv
      pure $ testGroup label
        [ testCase (resOp r) $
            Map.lookup (T.pack (resOp r)) expected @?=
              Just (resAbs r, resConc r)
        | r <- results
        ]
