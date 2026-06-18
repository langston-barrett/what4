{-
Module      : PrecisionRegression.SmoothClp
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Per-op precision results for the smooth-CLP domain at width 4. The CSV is at
@test\/PrecisionRegression\/smoothclp.csv@. Compare against @strides.csv@ to
quantify the precision cost of the smooth-stride over-approximation.
-}

{-# LANGUAGE DataKinds #-}

module PrecisionRegression.SmoothClp
  ( smoothClpEnum
  , results
  , csvPath
  ) where

import           Data.Bits ((.&.))

import qualified What4.Domains.BV.SmoothClp as SC

import           PrecisionRegression.Common

-- | Enumerate every proper 'SC.Domain' at width 4 (mirrors 'enumStrides4', but
-- 'SC.mk' smooths the stride, so 'dedup' collapses the coincidences).
enumSmoothClp4 :: [SC.Domain 4]
enumSmoothClp4 =
  [ SC.mk w4 start stride i
  | stride <- [1 .. mask4]
  , let g = stride .&. ((mask4 + 1) - stride)
  , let orbit = (mask4 + 1) `div` g
  , start <- [0 .. mask4]
  , i <- [0 .. orbit - 1]
  ]

smoothClpEnum :: DomainEnum (SC.Domain 4)
smoothClpEnum = DomainEnum (dedup SC.toList enumSmoothClp4) SC.toList

results :: [Result]
results =
  [ leqResult smoothClpEnum "leq" SC.leq
  , leqResult smoothClpEnum "leqPrecise" SC.leqPrecise
  , leqResult smoothClpEnum "leqExact" SC.leqExact
  , unaryResult smoothClpEnum "negate" (SC.negate w4) cNegate
  , binaryResult smoothClpEnum "add" (SC.add w4) cAdd
  , binaryResult smoothClpEnum "sub" (SC.sub w4) cSub
  , scaleResult smoothClpEnum (\k -> SC.scale w4 k)
  , binaryResult smoothClpEnum "mul" (SC.mul w4) cMul
  , binaryResultFiltered smoothClpEnum "udiv" (SC.udiv w4) cUdivPartial
  , binaryResultFiltered smoothClpEnum "urem" (SC.urem w4) cUremPartial
  , binaryResultFiltered smoothClpEnum "sdiv" (SC.sdiv w4) cSdivPartial
  , binaryResultFiltered smoothClpEnum "srem" (SC.srem w4) cSremPartial
  , binaryResult smoothClpEnum "udivSmtlib" (SC.udivSmtlib w4) cUdivSmtlib
  , binaryResult smoothClpEnum "uremSmtlib" (SC.uremSmtlib w4) cUremSmtlib
  , binaryResult smoothClpEnum "sdivSmtlib" (SC.sdivSmtlib w4) cSdivSmtlib
  , binaryResult smoothClpEnum "sremSmtlib" (SC.sremSmtlib w4) cSremSmtlib
  , unaryResult smoothClpEnum "not" (SC.not w4) cNot
  , binaryResult smoothClpEnum "andFast" (SC.andFast w4) cAnd
  , binaryResult smoothClpEnum "and" (SC.and w4) cAnd
  , binaryResult smoothClpEnum "andPrecise" (SC.andPrecise w4) cAnd
  , binaryResult smoothClpEnum "orFast" (SC.orFast w4) cOr
  , binaryResult smoothClpEnum "or" (SC.or w4) cOr
  , binaryResult smoothClpEnum "orPrecise" (SC.orPrecise w4) cOr
  , binaryResult smoothClpEnum "xor" (SC.xor w4) cXor
  , binaryResult smoothClpEnum "shl"  (SC.shl  w4) cShl
  , binaryResult smoothClpEnum "lshr" (SC.lshr w4) cLshr
  , binaryResult smoothClpEnum "ashr" (SC.ashr w4) cAshr
  , binaryResult smoothClpEnum "rol"  (SC.rol  w4) cRol
  , binaryResult smoothClpEnum "rolPrecise" (SC.rolPrecise w4) cRol
  , binaryResult smoothClpEnum "ror"  (SC.ror  w4) cRor
  , binaryResult smoothClpEnum "rorPrecise" (SC.rorPrecise w4) cRor
  , latticeMaybeResult smoothClpEnum "pseudoMeet" (SC.pseudoMeet w4) cMeet
  , latticeMaybeResult smoothClpEnum "pseudoMeetPrecise" (SC.pseudoMeetPrecise w4) cMeet
  , latticeUnderApproxMaybeResult smoothClpEnum "lowerBound" (SC.lowerBound w4) cMeet
  , latticeResult smoothClpEnum "pseudoJoin" (SC.pseudoJoin w4) cJoin
  , latticeResult smoothClpEnum "pseudoJoinPrecise" (SC.pseudoJoinPrecise w4) cJoin
  , latticeResult smoothClpEnum "boundingBoxJoin" (SC.boundingBoxJoin w4) cJoin
  , latticeMaybeResult smoothClpEnum "assumeUlt" (SC.assumeUlt w4) cAssumeUlt
  , latticeMaybeResult smoothClpEnum "assumeUle" (SC.assumeUle w4) cAssumeUle
  , latticeMaybeResult smoothClpEnum "assumeUgt" (SC.assumeUgt w4) cAssumeUgt
  , latticeMaybeResult smoothClpEnum "assumeUge" (SC.assumeUge w4) cAssumeUge
  , latticeMaybeResult smoothClpEnum "assumeSlt" (SC.assumeSlt w4) cAssumeSlt
  , latticeMaybeResult smoothClpEnum "assumeSle" (SC.assumeSle w4) cAssumeSle
  , latticeMaybeResult smoothClpEnum "assumeSgt" (SC.assumeSgt w4) cAssumeSgt
  , latticeMaybeResult smoothClpEnum "assumeSge" (SC.assumeSge w4) cAssumeSge
  , latticeMaybeResult smoothClpEnum "assumeSltPrecise" (SC.assumeSltPrecise w4) cAssumeSlt
  , latticeMaybeResult smoothClpEnum "assumeSlePrecise" (SC.assumeSlePrecise w4) cAssumeSle
  , latticeMaybeResult smoothClpEnum "assumeSgtPrecise" (SC.assumeSgtPrecise w4) cAssumeSgt
  , latticeMaybeResult smoothClpEnum "assumeSgePrecise" (SC.assumeSgePrecise w4) cAssumeSge
  ]

csvPath :: FilePath
csvPath = "test/PrecisionRegression/smoothclp.csv"
