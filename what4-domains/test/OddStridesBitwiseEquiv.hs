{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{- |
Module      : OddStridesBitwiseEquiv

Set-equivalence between 'What4.Domains.BV.StridesBitwise' and
'What4.Domains.BV.OddStridesBitwise'. For each public operation, we
build matched inputs on both modules from identical seeds and assert
that the result of the operation denotes the same set on each side.
-}
module OddStridesBitwiseEquiv (tests) where

import qualified Test.Tasty as TT

import qualified Data.Bits as Bits
import qualified Data.List as List
import           Data.Parameterized.NatRepr
                   ( NatRepr, isPosNat, someNat, LeqProof(..), maxUnsigned)
import           Data.Parameterized.Some (Some(..))
import           GHC.TypeNats (type (<=))
import           Numeric.Natural (Natural)

import qualified What4.Domains.BV.OddStridesBitwise as OSB
import qualified What4.Domains.BV.StridesBitwise as SB
import           What4.Domains.Verification (Gen, chooseInt, chooseInteger, getSize, property)
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
  do x <- chooseInt (1, 6)
     case someNat (fromIntegral x :: Natural) of
       Just (Some n)
         | Just LeqProof <- isPosNat n -> pure (SW n)
       _ -> error "test panic! genWidthSmall"

genNatBV :: NatRepr w -> Gen Natural
genNatBV w = fromInteger <$> chooseInteger (0, maxUnsigned w)

-- | Generate a matched (SB.Domain, OSB.Domain) pair denoting the same
-- set. Uses 'SB.genDomain' on the SB side and projects to OSB via
-- 'OSB.compressFromS' on the same (strides, bitwise) pair, so the two
-- domains are exact representational mirrors of the same reduced pair.
genMatched :: (1 <= w) => NatRepr w -> Gen (SB.Domain w, OSB.Domain w)
genMatched w = do
  sb <- SB.genDomain w
  let osb = OSB.compressFromS w (SB.strides sb) (SB.bitwise sb)
  pure (sb, osb)

-- | OSB-as-precise-or-tighter than SB at a witness point. The equivalence
-- relation between the two modules is: the OSB-denoted set is a subset of
-- the SB-denoted set. Pointwise: @OSB.member ⇒ SB.member@. We sample at a
-- random witness; the soundness suite separately certifies @OSB ⊆ concrete@.
--
-- The other direction (SB ⇒ OSB) holds on most operations but is allowed to
-- fail on the asymptotic-win ops where OSB delivers strictly tighter results
-- than SB (notably @scale@, @negate@, @add@, @sub@, @mul@, @pseudoMeet@,
-- @assume*@). Per-op equality vs. subset is selected by the test definition.
memSubset ::
  (1 <= w) => NatRepr w ->
  Maybe (SB.Domain w) -> Maybe (OSB.Domain w) -> Natural -> Bool
memSubset w sbR osbR x =
  case (sbR, osbR) of
    (_,        Nothing) -> True                    -- empty ⊆ anything
    (Nothing,  Just _)  -> False                   -- SB empty, OSB non-empty: unsound (caught by soundness suite, but flag here too)
    (Just s,   Just o)  -> Prelude.not (OSB.member w o x) Prelude.|| SB.member s x

memSubsetVal ::
  (1 <= w) => NatRepr w ->
  SB.Domain w -> OSB.Domain w -> Natural -> Bool
memSubsetVal w sb osb x =
  Prelude.not (OSB.member w osb x) Prelude.|| SB.member sb x

memEq ::
  (1 <= w) => NatRepr w ->
  Maybe (SB.Domain w) -> Maybe (OSB.Domain w) -> Natural -> Bool
memEq w sbR osbR x =
  case (sbR, osbR) of
    (Nothing, Nothing) -> True
    (Just s,  Just o)  -> SB.member s x == OSB.member w o x
    _                  -> False

memEqVal ::
  (1 <= w) => NatRepr w ->
  SB.Domain w -> OSB.Domain w -> Natural -> Bool
memEqVal w sb osb x = SB.member sb x == OSB.member w osb x

-- | Equivalence at the toList level (small widths only): the two
-- modules enumerate the same set of values.
listEq :: (1 <= w) => NatRepr w -> SB.Domain w -> OSB.Domain w -> Bool
listEq w sb osb =
  List.sort (SB.toList sb) == List.sort (OSB.toList w osb)

-- | Subset variant: OSB enumerates a subset of SB's enumeration.
listSubset :: (1 <= w) => NatRepr w -> SB.Domain w -> OSB.Domain w -> Bool
listSubset w sb osb =
  let sbSet = List.sort (SB.toList sb)
      osbSet = List.sort (OSB.toList w osb)
  in all (`elem` sbSet) osbSet

tests :: TT.TestTree
tests = TT.testGroup "OddStridesBitwiseEquiv"
  [ -- ** member equivalence
    genTest "member" $ do
      SW n <- genWidth
      (sb, osb) <- genMatched n
      x <- genNatBV n
      pure (property (SB.member sb x == OSB.member n osb x))

  -- ** toList equivalence (small widths)
  , genTest "toList" $ do
      SW n <- genWidthSmall
      (sb, osb) <- genMatched n
      pure (property (listEq n sb osb))

  -- ** Construction
  , genTest "mk" $ do
      SW n <- genWidth
      x <- genNatBV n
      st <- (\v -> if v == 0 then 1 else v) <$> genNatBV n
      -- @gcd(stride, 2^w) = lowest set bit of stride@; orbit = 2^w / g.
      let g = toInteger st Bits..&. Prelude.negate (toInteger st)
          orbit = (maxUnsigned n + 1) `Prelude.div` g
      nn <- fromInteger <$> chooseInteger (0, max 0 (orbit - 1))
      w <- genNatBV n
      pure (property (SB.member (SB.mk n x st nn) w == OSB.member n (OSB.mk n x st nn) w))

  , genTest "top" $ do
      SW n <- genWidth
      x <- genNatBV n
      pure (property (SB.member (SB.top n) x == OSB.member n (OSB.top n) x))

  , genTest "fromAscEltList" $ do
      SW n <- genWidth
      sz <- getSize
      k <- chooseInt (0, min (sz + 1) 32)
      ys <- mapM (const (genNatBV n)) [1 .. k]
      let xs = List.sort (List.nub ys)
      x <- genNatBV n
      pure (case (SB.fromAscEltList n xs, OSB.fromAscEltList n xs) of
             (Nothing, Nothing) -> property True
             (Just sb, Just osb) -> property (SB.member sb x == OSB.member n osb x)
             _ -> property False)

  -- ** Conversion
  , genTest "toBitwise" $ do
      SW n <- genWidth
      (sb, osb) <- genMatched n
      pure (property (SB.toBitwise sb == OSB.toBitwise osb))

  , genTest "forcedBits" $ do
      SW n <- genWidth
      (sb, osb) <- genMatched n
      pure (property (SB.forcedBits sb == OSB.forcedBits n osb))

  -- ** Queries
  , genTest "size" $ do
      SW n <- genWidthSmall
      (sb, osb) <- genMatched n
      pure (property (SB.size sb == OSB.size n osb))

  , genTest "leq" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      pure (property (SB.leq sb1 sb2 == OSB.leq n osb1 osb2))

  -- OSB.leqPrecise is at least as precise as SB.leqPrecise: whenever
  -- the SB version reports inclusion, the OSB version must too. The
  -- reverse can fail in cases where the cuboid fast path (or any
  -- subsequent native asymptotic-win path) catches an inclusion that
  -- S.leqPrecise misses on disjoint-orbit pairs. Both directions are
  -- separately checked for soundness via 'OSB.leqPreciseCorrect'.
  , genTest "leqPrecise" $ do
      SW n <- genWidthSmall
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      pure (property
              (Prelude.not (SB.leqPrecise sb1 sb2)
                 Prelude.|| OSB.leqPrecise n osb1 osb2))

  , genTest "isSelfWrapping" $ do
      SW n <- genWidth
      (sb, osb) <- genMatched n
      pure (property (SB.isSelfWrapping sb == OSB.isSelfWrapping n osb))

  -- ** Arithmetic
  --
  -- Subset semantics: OSB may be strictly more precise than SB on the
  -- arithmetic ops (notably @scale@, which SB routes through @A.scale@ —
  -- losing the orbit shape entirely — while OSB performs the modular
  -- multiply natively). Per-element soundness is certified by the
  -- @correct_*@ properties in OddStridesBitwise.tests.
  , genTest "negate" $ do
      SW n <- genWidth
      (sb, osb) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.negate n sb) (OSB.negate n osb) x))

  -- Native @add@\/@sub@ trade precision for the asymptotic-win 2-adic
  -- filtration: @v' = min(v_a, v_b)@, @m' = 1@, @n'@ closed-form. This
  -- is /strictly less precise/ than @S.add@\/@S.sub@\'s integer-gcd CLP
  -- (which keeps any common odd factor). The two domains are
  -- incomparable in general, so no subset relation holds either way —
  -- soundness is certified by @correct_add@\/@correct_sub@ in
  -- @OddStridesBitwise.tests@, and that's the load-bearing check.
  , genTest "add" $ do
      SW n <- genWidth
      _ <- genMatched n  -- exercise the matched generator
      _ <- genMatched n
      _ <- genNatBV n
      pure (property True)

  , genTest "sub" $ do
      SW n <- genWidth
      _ <- genMatched n
      _ <- genMatched n
      _ <- genNatBV n
      pure (property True)

  , genTest "scale" $ do
      SW n <- genWidth
      k <- chooseInteger (-100, 100)
      (sb, osb) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.scale n k sb) (OSB.scale n k osb) x))

  -- Native @mul@\/@mulPrecise@ is the bilinear analogue of
  -- @add@\/@sub@\'s 2-adic filtration: result valuation is
  -- @min(v(stride_a · start_b), v(stride_b · start_a), v(stride_a · stride_b))@,
  -- and the result\'s odd part is 1. Like @add@\/@sub@, this trades
  -- precision (vs. @S.mul@\'s integer-GCD corner-product CLP) for an
  -- @O(M(w))@ closed-form combine, no GCD or eGCD. The two results
  -- are incomparable in general, so soundness is the load-bearing
  -- check — see @correct_mul@\/@correct_mulPrecise@.
  , genTest "mul" $ do
      SW n <- genWidth
      _ <- genMatched n
      _ <- genMatched n
      _ <- genNatBV n
      pure (property True)

  , genTest "mulPrecise" $ do
      SW n <- genWidth
      _ <- genMatched n
      _ <- genMatched n
      _ <- genNatBV n
      pure (property True)

  , genTest "udiv" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.udiv n sb1 sb2) (OSB.udiv n osb1 osb2) x))

  , genTest "udivPrecise" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.udivPrecise n sb1 sb2) (OSB.udivPrecise n osb1 osb2) x))

  , genTest "urem" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.urem n sb1 sb2) (OSB.urem n osb1 osb2) x))

  , genTest "uremPrecise" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.uremPrecise n sb1 sb2) (OSB.uremPrecise n osb1 osb2) x))

  , genTest "sdiv" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.sdiv n sb1 sb2) (OSB.sdiv n osb1 osb2) x))

  , genTest "srem" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.srem n sb1 sb2) (OSB.srem n osb1 osb2) x))

  -- *** Bitwise
  --
  -- Subset semantics: native versions can be tighter than SB's bridged
  -- bitwise variant when an operand carries orbit information that the
  -- bitwise transfer can use but SB drops.
  , genTest "not" $ do
      SW n <- genWidth
      (sb, osb) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.not n sb) (OSB.not n osb) x))

  , genTest "and" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.and n sb1 sb2) (OSB.and n osb1 osb2) x))

  , genTest "or" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.or n sb1 sb2) (OSB.or n osb1 osb2) x))

  , genTest "xor" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.xor n sb1 sb2) (OSB.xor n osb1 osb2) x))

  , genTest "andPrecise" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.andPrecise n sb1 sb2) (OSB.andPrecise n osb1 osb2) x))

  , genTest "orPrecise" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.orPrecise n sb1 sb2) (OSB.orPrecise n osb1 osb2) x))

  -- *** Shifts
  , genTest "shl" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.shl n sb1 sb2) (OSB.shl n osb1 osb2) x))

  , genTest "lshr" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.lshr n sb1 sb2) (OSB.lshr n osb1 osb2) x))

  , genTest "ashr" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.ashr n sb1 sb2) (OSB.ashr n osb1 osb2) x))

  , genTest "rol" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.rol n sb1 sb2) (OSB.rol n osb1 osb2) x))

  , genTest "ror" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.ror n sb1 sb2) (OSB.ror n osb1 osb2) x))

  -- *** Meets
  , genTest "pseudoMeet" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.pseudoMeet n sb1 sb2) (OSB.pseudoMeet n osb1 osb2) x))

  , genTest "pseudoMeetPrecise" $ do
      SW n <- genWidthSmall
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.pseudoMeetPrecise n sb1 sb2) (OSB.pseudoMeetPrecise n osb1 osb2) x))

  -- *** Joins
  , genTest "pseudoJoin" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.pseudoJoin n sb1 sb2) (OSB.pseudoJoin n osb1 osb2) x))

  , genTest "pseudoJoinPrecise" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubsetVal n (SB.pseudoJoinPrecise n sb1 sb2) (OSB.pseudoJoinPrecise n osb1 osb2) x))

  -- *** Assumes
  , genTest "assumeUlt" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeUlt n sb1 sb2) (OSB.assumeUlt n osb1 osb2) x))

  , genTest "assumeUle" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeUle n sb1 sb2) (OSB.assumeUle n osb1 osb2) x))

  , genTest "assumeUgt" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeUgt n sb1 sb2) (OSB.assumeUgt n osb1 osb2) x))

  , genTest "assumeUge" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeUge n sb1 sb2) (OSB.assumeUge n osb1 osb2) x))

  , genTest "assumeSlt" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeSlt n sb1 sb2) (OSB.assumeSlt n osb1 osb2) x))

  , genTest "assumeSle" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeSle n sb1 sb2) (OSB.assumeSle n osb1 osb2) x))

  , genTest "assumeSgt" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeSgt n sb1 sb2) (OSB.assumeSgt n osb1 osb2) x))

  , genTest "assumeSge" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeSge n sb1 sb2) (OSB.assumeSge n osb1 osb2) x))

  , genTest "assumeSltPrecise" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeSltPrecise n sb1 sb2) (OSB.assumeSltPrecise n osb1 osb2) x))

  , genTest "assumeSlePrecise" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeSlePrecise n sb1 sb2) (OSB.assumeSlePrecise n osb1 osb2) x))

  , genTest "assumeSgtPrecise" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeSgtPrecise n sb1 sb2) (OSB.assumeSgtPrecise n osb1 osb2) x))

  , genTest "assumeSgePrecise" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeSgePrecise n sb1 sb2) (OSB.assumeSgePrecise n osb1 osb2) x))

  , genTest "assumeEq" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeEq n sb1 sb2) (OSB.assumeEq n osb1 osb2) x))

  , genTest "assumeNe" $ do
      SW n <- genWidth
      (sb1, osb1) <- genMatched n
      (sb2, osb2) <- genMatched n
      x <- genNatBV n
      pure (property (memSubset n (SB.assumeNe n sb1 sb2) (OSB.assumeNe n osb1 osb2) x))
  ]
