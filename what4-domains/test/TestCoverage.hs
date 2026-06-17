{-
Module      : TestCoverage
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Test-coverage tests: tests that require certain other tests to exist.

These guard against drift between the Cryptol specification (in @doc\/*.cry@),
the Haskell @correct_*@ predicates that transliterate it (in "What4.Domains.BV"
and submodules), and the property-based tests that exercise those predicates (in
@test\/BVDomTests.hs@).

Two correspondences are checked:

  * Cryptol \<-\> Haskell: bidirectional. Every property defined in the Cryptol
    specs has a same-named Haskell property, or is on an explicit allowlist
    of predicates that are intentionally not translated; and conversely
    every Haskell property has a same-named Cryptol counterpart, or is on a
    Haskell-only allowlist.

  * Haskell \<-\> PBT: every Haskell property defined in the abstract-domain
    modules is invoked at least once in @BVDomTests.hs@. Note: the reverse
    direction (test invokes a non-existent Haskell predicate) is trivially
    enforced by GHC.

The allowlists are small and documented inline; growing them should be a
deliberate choice. Files are read at test-runtime relative to the package root
(which is the working directory used by @cabal test@).
-}

{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           Control.Monad (forM)
import           Data.Char (isAlphaNum)
import           Data.List (tails)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Test.Tasty as TT
import           Test.Tasty.HUnit

-- | A Haskell source file holding properties, together with the qualifier under
-- which the test driver imports it, and the test file that should invoke its
-- properties.
data HsModule = HsModule
  { hsModFile :: FilePath
  , hsModQual :: Text
  , hsModTestFile :: FilePath
  }

arithMod, bitwiseMod, xorMod, overallMod, stridesMod, stridesBitwiseMod, oddStridesBitwiseMod, stridedMod :: HsModule
arithMod             = HsModule "src/What4/Domains/BV/Arith.hs"              "A"   "test/BVDomTests.hs"
bitwiseMod           = HsModule "src/What4/Domains/BV/Bitwise.hs"            "B"   "test/BVDomTests.hs"
xorMod               = HsModule "src/What4/Domains/BV/XOR.hs"                "X"   "test/BVDomTests.hs"
overallMod           = HsModule "src/What4/Domains/BV.hs"                    "O"   "test/BVDomTests.hs"
stridesMod           = HsModule "src/What4/Domains/BV/Strides.hs"            "S"   "test/Strides.hs"
stridesBitwiseMod    = HsModule "src/What4/Domains/BV/StridesBitwise.hs"     "SB"  "test/StridesBitwise.hs"
oddStridesBitwiseMod = HsModule "src/What4/Domains/BV/OddStridesBitwise.hs"  "OSB" "test/OddStridesBitwise.hs"
stridedMod           = HsModule "src/What4/Domains/BV/StridedInterval.hs"    "S"   "test/StridedInterval.hs"

-- | All Haskell-side modules whose properties are exercised by the
-- property-test driver. The invocation check runs against every module
-- in this list.
allHsModules :: [HsModule]
allHsModules =
  [arithMod, bitwiseMod, xorMod, overallMod, stridesMod, stridesBitwiseMod, oddStridesBitwiseMod, stridedMod]

-- | Modules backed by a Cryptol model (in @doc/*.cry@). The
-- Cryptol-correspondence checks run only against these.
-- 'stridesBitwiseMod' is excluded because it's a reduced product
-- assembled from primitives that already have Cryptol models — its own
-- Haskell-only properties have no Cryptol counterpart.
cryptolBackedModules :: [HsModule]
cryptolBackedModules =
  [arithMod, bitwiseMod, xorMod, overallMod, stridesMod, stridedMod]

-- | Additional source files that define Haskell @Property@ predicates but
-- aren't themselves checked for invocation. Currently used to satisfy the
-- Cryptol\<-\>Haskell correspondence check for properties (like @precise_*@)
-- that live in the test suite rather than under @src/@.
additionalHsPropertyFiles :: [FilePath]
additionalHsPropertyFiles =
  [ "test/Strides/Precision.hs"
  ]

cryptolFiles :: [FilePath]
cryptolFiles =
  [ "doc/arithdomain.cry"
  , "doc/bitsdomain.cry"
  , "doc/xordomain.cry"
  , "doc/bvdomain.cry"
  , "doc/strides.cry"
  , "doc/strideddomain.cry"
  ]

main :: IO ()
main = TT.defaultMain $ TT.testGroup "Test coverage"
  [ haskellInvocationTests
  , cryptolCorrespondenceTests
  , exportOrderTests
  ]

------------------------------------------------------------------------
-- Haskell <-> PBT correspondence: every Haskell property is invoked from
-- BVDomTests

haskellInvocationTests :: TT.TestTree
haskellInvocationTests = TT.testGroup "Haskell predicates are invoked"
  [ testCase (hsModFile m) (checkModuleInvoked m) | m <- allHsModules ]

checkModuleInvoked :: HsModule -> Assertion
checkModuleInvoked m = do
  src     <- TIO.readFile (hsModFile m)
  testSrc <- TIO.readFile (hsModTestFile m)
  let names = extractHsPredicates src
  assertNonEmpty (hsModFile m) "Property" names
  let missing = [ n | n <- names, not (isInvokedAs (hsModQual m) n testSrc) ]
  case missing of
    [] -> pure ()
    _  -> assertFailure $ T.unpack $ T.unlines $
            ("Predicates defined in " <> T.pack (hsModFile m)
             <> " but never invoked as " <> hsModQual m <> ".<name> in "
             <> T.pack (hsModTestFile m) <> ":")
            : map ("  " <>) (Set.toAscList (Set.fromList missing))

-- | Sanity check: the source extractor should always find at least one property
-- in each scanned file. An empty result usually means the extractor is broken
-- (e.g., signature syntax changed).
assertNonEmpty :: FilePath -> Text -> [a] -> Assertion
assertNonEmpty f tyName xs =
  case xs of
    [] -> assertFailure $ T.unpack $
            "TestCoverage extractor found no " <> tyName
            <> " predicates in " <> T.pack f
            <> " - the extractor may be broken or the file is empty."
    _  -> pure ()

-- | True if @qual.name@ appears in @src@ as a token (not as a prefix of a
-- longer identifier).
isInvokedAs :: Text -> Text -> Text -> Bool
isInvokedAs qual name src = go src
  where
    needle = qual <> "." <> name
    go t =
      case T.breakOn needle t of
        (_, rest)
          | T.null rest -> False
          | otherwise ->
              let suffix = T.drop (T.length needle) rest in
              case T.uncons suffix of
                Just (c, _) | isIdentChar c -> go suffix
                _ -> True

------------------------------------------------------------------------
-- Cryptol <-> Haskell correspondence: every Cryptol property has a Haskell
-- counterpart and vice versa

-- | Cryptol predicates that are intentionally not translated into a Haskell
-- property.
--
-- @ule@\/@sle@: Haskell's three-valued @ult@\/@slt :: Maybe Bool@ already
-- covers the strict-less-than direction; supporting Cryptol's @ule@\/@sle@
-- would require new public functions.
--
-- @shrinkRange@: There is no separate @shrinkRange@ helper on the Haskell side.
cryptolOnly :: Set.Set Text
cryptolOnly = Set.fromList
  [ "correct_ule"
  , "correct_sle"
  , "correct_shrinkRange"
  -- Diophantine helpers in 'What4.Domains.BV.Strides.Internal' have direct
  -- Haskell unit tests in @test/Strides/Internal.hs@, but those tests are
  -- inlined inside 'genTest' calls rather than top-level @Property@-returning
  -- predicates, so the extractor doesn't pick them up.
  , "eGCD_bezout", "eGCD_nonNegative"
  , "ceilDivPosCorrect", "floorDivPosCorrect"
  , "solveLinearDiophantineSound"
  ]

-- | Haskell predicates that intentionally have no Cryptol counterpart.
--
-- @correct_*Smtlib@: No Cryptol spec as of yet.
--
-- @correct_eq@\/@correct_testBit@\/@correct_bitbounds@\/
-- @correct_select@\/@correct_scale_eq@: Haskell-only helpers.
--
-- @correct_asXorDomain@\/@correct_fromXorDomain@: overall-domain \<-\> XOR
-- conversions on @BVDomain@.  Cryptol has no unified @BVDomain@ type (see
-- #401), so the per-subdomain transfer predicates (@correct_arithToXorDomain@,
-- @correct_bitwiseToXorDomain@, @correct_xorToBitwiseDomain@) already cover
-- this ground.
--
-- @precise_overlap@: again, no @BVDomain@, see #401.
--
-- @correct_equiv_*Abstract@: equivalence between the optimized
-- Haskell shift-by-domain impl and its reference spec; the Cryptol
-- side has a single declarative implementation so there's nothing to
-- compare against.
haskellOnly :: Set.Set Text
haskellOnly = Set.fromList
  [ "correct_udivSmtlib", "correct_uremSmtlib"
  , "correct_sdivSmtlib", "correct_sremSmtlib"
  , "correct_eq", "correct_testBit", "correct_bitbounds"
  , "correct_select", "correct_scale_eq"
  , "correct_asXorDomain", "correct_fromXorDomain"
  , "precise_overlap"
  , "correct_equiv_shlAbstract", "correct_equiv_lshrAbstract"
  , "correct_equiv_ashrAbstract"
  , "correct_equiv_rolAbstract", "correct_equiv_rorAbstract"
  -- 'toList' enumerates a progression's contents; the natural specification is an
  -- unbounded list, which Cryptol's fixed-size sequences can't represent
  -- directly. The 'memberBottom' Cryptol property already pins down 'member'
  -- on the bottom case, so the toList round-trips are Haskell-only.
  , "toListMember", "memberToList", "toListNoDuplicates"
  , "sizeViaToList"
  , "isSelfWrappingViaToList"
  -- 'fromAscEltList' takes an arbitrary-length list of elements, which
  -- Cryptol's fixed-size sequences can't represent directly. The
  -- 'fromAscEltListToListExactNonWrapping' round-trip also uses 'toList'.
  , "fromAscEltListMember"
  , "fromAscEltListToListExactNonWrapping"
  -- 'firstCosetMemberCorrect' uses parametric width and shift amounts that
  -- are difficult to express in Cryptol's type system.
  , "firstCosetMemberCorrect"
  -- 'orbitLenViaToList' relies on 'toList' which has no direct Cryptol spec.
  , "orbitLenViaToList"
  -- 'canonHashRespectsEq' checks the 'Hashable' law for the 'Canonical'
  -- newtype; Cryptol has no 'Hashable', so this is Haskell-only.
  , "canonHashRespectsEq"
  -- 'floorSum' is a Haskell-only Euclidean-recursion helper used by
  -- 'leqExact'; the Cryptol mirror states 'leqExact' declaratively.
  , "floorSumCorrect"
  -- 'leqExactWindow' is the Haskell-only 'floorSum'-based window count behind
  -- 'leqExact'\''s fallback; the Cryptol 'leqExact' oracle covers that case
  -- declaratively, so this validates the Haskell branch only.
  , "leqExactWindowAgrees"
  -- 'compactify' merges adjacent progressions when their union is itself a
  -- progression. Mirroring the Haskell fixed-point iteration in Cryptol
  -- is impractical for symbolic verification.
  , "correct_compactify"
  -- 'exactJoin' and 'exactMeet' are partial operators built on
  -- 'compactify'; they share the same Cryptol-mirroring difficulty.
  , "correct_exactJoin"
  , "exactJoinCommutative", "exactJoinIdempotent", "exactJoinUpperBound"
  , "exactJoinTopAnnihilator", "exactJoinAssociative"
  , "correct_exactMeet"
  , "exactMeetCommutative", "exactMeetIdempotent", "exactMeetLowerBound"
  , "exactMeetTopIdentity", "exactMeetAssociative"
  ]

cryptolCorrespondenceTests :: TT.TestTree
cryptolCorrespondenceTests = TT.testGroup "Cryptol <-> Haskell"
  [ TT.testGroup "Cryptol predicates have Haskell counterparts"
      [ testCase f (checkCryptolFile f) | f <- cryptolFiles ]
  , TT.testGroup "Haskell predicates have Cryptol counterparts"
      [ testCase (hsModFile m) (checkHaskellFile m) | m <- cryptolBackedModules ]
  ]

checkCryptolFile :: FilePath -> Assertion
checkCryptolFile f = do
  cryptolSrc <- TIO.readFile f
  hsNames <-
    fmap Set.unions $
      forM (map hsModFile allHsModules ++ additionalHsPropertyFiles) $ \path -> do
        content <- TIO.readFile path
        pure (Set.fromList (extractHsPredicates content))
  let cryptolNames = extractCryPredicates cryptolSrc
  assertNonEmpty f "Property" cryptolNames
  let missing = [ cn | cn <- cryptolNames
                     , not (Set.member cn cryptolOnly)
                     , not (Set.member cn hsNames)
                     ]
  case missing of
    [] -> pure ()
    _  -> assertFailure $ T.unpack $ T.unlines $
            ("Cryptol predicates in " <> T.pack f
             <> " with no matching Haskell counterpart:")
            : map ("  " <>) missing

checkHaskellFile :: HsModule -> Assertion
checkHaskellFile m = do
  hsSrc <- TIO.readFile (hsModFile m)
  cryNames <-
    fmap Set.unions $ 
      forM cryptolFiles $ \path -> do
        content <- TIO.readFile path
        pure (Set.fromList (extractCryPredicates content))
  let hsNames = extractHsPredicates hsSrc
  assertNonEmpty (hsModFile m) "Property" hsNames
  let missing = [ hn | hn <- hsNames
                     , not (Set.member hn haskellOnly)
                     , not (Set.member hn cryNames)
                     ]
  case missing of
    [] -> pure ()
    _  -> assertFailure $ T.unpack $ T.unlines $
            ("Haskell predicates in " <> T.pack (hsModFile m)
             <> " with no matching Cryptol counterpart in doc/*.cry:")
            : map ("  " <>) missing

------------------------------------------------------------------------
-- Export order matches definition order; export sections match body sections

exportOrderTests :: TT.TestTree
exportOrderTests = TT.testGroup "Export order matches definition order"
  [ testCase "src/What4/Domains/BV/Strides.hs" $
      checkExportOrderFor "src/What4/Domains/BV/Strides.hs"
  , testCase "src/What4/Domains/BV/StridesBitwise.hs" $
      checkExportOrderFor "src/What4/Domains/BV/StridesBitwise.hs"
  , testCase "src/What4/Domains/BV/OddStridesBitwise.hs" $
      checkExportOrderFor "src/What4/Domains/BV/OddStridesBitwise.hs"
  , testCase "StridesBitwise mirrors Strides section order" $
      checkSectionsMirrorStrides "src/What4/Domains/BV/StridesBitwise.hs"
  , testCase "StridesBitwise mirrors Strides operation order within sections" $
      checkOpOrderMirrorsStrides "src/What4/Domains/BV/StridesBitwise.hs"
  , testCase "OddStridesBitwise mirrors Strides section order" $
      checkSectionsMirrorStrides "src/What4/Domains/BV/OddStridesBitwise.hs"
  , testCase "OddStridesBitwise mirrors Strides operation order within sections" $
      checkOpOrderMirrorsStrides "src/What4/Domains/BV/OddStridesBitwise.hs"
  ]

-- | Run all the per-file export-order checks on a single file.
checkExportOrderFor :: FilePath -> Assertion
checkExportOrderFor f = do
  src <- TIO.readFile f
  checkExportOrder         f src
  checkExportSections      f src
  checkSectionNesting      f src
  checkPropertiesMatchOps  f src

-- | Section header sequence in a wrapper's export list must be a
-- subsequence of Strides' (the wrapper omits some sections like
-- "Reduced product with bitwise" or "Internal helpers" but never
-- reorders).
checkSectionsMirrorStrides :: FilePath -> Assertion
checkSectionsMirrorStrides wrapperFile = do
  stridesSrc  <- TIO.readFile "src/What4/Domains/BV/Strides.hs"
  wrapperSrc  <- TIO.readFile wrapperFile
  let stridesSecs = extractExportSections stridesSrc
      -- Sections a wrapper legitimately introduces that Strides lacks:
      -- 'OddStridesBitwise' groups its power-of-two fast-path correctness
      -- properties under their own subsection (the 2-adic representation
      -- gives these ops a closed form the plain 'Strides' module has no
      -- counterpart for).
      newWrapperSections = Set.fromList
        [ "-- *** Power-of-2 fast paths" ]
      wrapperSecs = filter (`Set.notMember` newWrapperSections)
                           (extractExportSections wrapperSrc)
  case firstNotInSubsequence wrapperSecs stridesSecs of
    Nothing -> pure ()
    Just bad -> assertFailure $ T.unpack $
      "Section header in " <> T.pack wrapperFile
      <> " not a subsequence of Strides.hs at: '"
      <> bad <> "'"

-- | For each section header that appears in both Strides and the
-- wrapper's export lists, the exported names in the wrapper under that
-- section must be a subsequence of Strides' names under the same
-- section, in order.
checkOpOrderMirrorsStrides :: FilePath -> Assertion
checkOpOrderMirrorsStrides wrapperFile = do
  stridesSrc <- TIO.readFile "src/What4/Domains/BV/Strides.hs"
  wrapperSrc <- TIO.readFile wrapperFile
  let stridesSecs = exportListSectioned stridesSrc
      wrapperSecs = exportListSectioned wrapperSrc
      shared = [ (sec, sNames, wNames)
               | (sec, sNames) <- stridesSecs
               , Just wNames <- [lookup sec wrapperSecs]
               , not (T.null sec)  -- skip pre-section items (Domain accessors, etc.)
               ]
      -- Names that StridesBitwise exports legitimately even though
      -- Strides doesn't: variants present in Bitwise that wrap-induce
      -- in the reduced product.
      newWrapperNames = Set.fromList
        [ -- 'mkReduced' is the reduced-product constructor (build a 'Domain'
          -- from a strides + bitwise component); the plain 'Strides' module
          -- has no such pairing constructor.
          "mkReduced"
        , "mulPrecise", "udivPrecise", "uremPrecise"
        , "correct_mulPrecise", "correct_udivPrecise", "correct_uremPrecise"
        -- Reduced-product-only 'size' properties (no strides counterpart).
        , "sizeAtMostComponents", "sizeExactCorrect", "windowMarginalCount"
        , "uniformWindowBalanced", "pinsConflictEmpty"
        -- Equality-branch assume: the strides domain has no 'assumeEq' (the
        -- product routes it through 'pseudoMeet'), so these names are
        -- product-only.
        , "assumeEq", "correct_assumeEq"
        -- OSB's native-core checks (under "Reduced product with bitwise"):
        -- the 2-adic GCD primitives and native meet\/leq routines have no
        -- counterpart among Strides' reduced-product properties.
        , "gcdOddMatchesPrelude", "binGcdMatchesPrelude"
        , "nativeLeqPreciseMatchesBridge", "native2AdicMeetMatchesBridge"
        , "nativeLeqExactMatchesBridge", "nativeReduceMatchesBridge"
        ]
      mismatches = [ (sec, bad)
                   | (sec, sNames, wNames) <- shared
                   , let wNames' = filter (`Set.notMember` newWrapperNames) wNames
                   , Just bad <- [firstNotInSubsequence wNames' sNames]
                   ]
  case mismatches of
    [] -> pure ()
    _  -> assertFailure $ T.unpack $ T.unlines $
            ("Operations in " <> T.pack wrapperFile
             <> " not a subsequence of Strides.hs in some section:") :
            [ "  section " <> sec <> ": '" <> nm <> "'" | (sec, nm) <- mismatches ]

-- | Find the first element of @xs@ that does not appear in @ys@ (in
-- order). Returns 'Nothing' if @xs@ is a subsequence of @ys@.
firstNotInSubsequence :: [Text] -> [Text] -> Maybe Text
firstNotInSubsequence []     _  = Nothing
firstNotInSubsequence (x:xs) ys =
  case dropWhile (/= x) ys of
    []     -> Just x
    (_:rest) -> firstNotInSubsequence xs rest

-- | Split an export list into @[(sectionHeader, [exportName])]@,
-- preserving order. The first section's header is the empty string
-- (for items declared before any @-- *@ header).
exportListSectioned :: Text -> [(Text, [Text])]
exportListSectioned src =
  reverse (go "" [] [] (exportListLines src))
  where
    go cur acc result [] = (cur, reverse acc) : result
    go cur acc result (l:ls)
      | "-- *" `T.isPrefixOf` T.stripStart l =
          go (T.stripStart l) [] ((cur, reverse acc) : result) ls
      | Just nm <- exportNameOf l =
          go cur (nm : acc) result ls
      | otherwise = go cur acc result ls

    exportNameOf l = case T.stripStart l of
      t | Just t' <- T.stripPrefix ", " t ->
            let nm = T.takeWhile isIdentChar t'
            in if T.null nm then Nothing else Just nm
        | Just t' <- T.stripPrefix "( " t ->
            let nm = T.takeWhile isIdentChar t'
            in if T.null nm then Nothing else Just nm
      _ -> Nothing

-- | Assert that exported names appear in the same order as their definitions.
checkExportOrder :: FilePath -> Text -> Assertion
checkExportOrder f src = do
  let exports = extractExports src
      defs    = extractDefs src
  assertNonEmpty f "export" exports
  assertNonEmpty f "definition" defs
  case firstOutOfOrder exports defs of
    Nothing    -> pure ()
    Just (a, b) -> assertFailure $ T.unpack $
      "In " <> T.pack f <> ": '" <> a
      <> "' is exported before '" <> b
      <> "' but defined after it"

-- | Assert that @-- *@-family section headers in the export list appear in the
-- same relative order in the body. Exact text matching means @-- *@ and
-- @-- **@ headers are never treated as the same. Headers with no body
-- counterpart are silently skipped.
checkExportSections :: FilePath -> Text -> Assertion
checkExportSections f src = do
  let expSecs  = extractExportSections src
      bodySecs = extractBodySections src
  assertNonEmpty f "export section" expSecs
  assertNonEmpty f "body section" bodySecs
  case firstOutOfOrder expSecs bodySecs of
    Nothing     -> pure ()
    Just (a, b) -> assertFailure $ T.unpack $
      "In " <> T.pack f <> ": export section '" <> a
      <> "' comes before '" <> b
      <> "' in the export list but after it in the body"

-- | Assert that section headers are properly nested: a header at depth @d@ may
-- only appear after a header at depth @d - 1@ (or @d@) has been seen. E.g.
-- @-- ***@ requires a prior @-- **@. Checked in both the export list and body.
checkSectionNesting :: FilePath -> Text -> Assertion
checkSectionNesting f src = do
  checkNesting "export list" (extractExportSections src)
  checkNesting "body"        (extractBodySections src)
  where
    checkNesting loc secs =
      case badNesting secs of
        Nothing      -> pure ()
        Just (d, hd) -> assertFailure $ T.unpack $
          "In " <> T.pack f <> " " <> loc <> ": section '" <> hd
          <> "' at depth " <> T.pack (show d)
          <> " has no enclosing section at depth " <> T.pack (show (d - 1))

    badNesting secs = go 0 secs
      where
        go _    []     = Nothing
        go maxD (h:hs) =
          let d = secDepth h
          in if d > maxD + 1
               then Just (d, h)
               else go (max maxD d) hs

-- | Assert that the @-- **@ subsections under @-- * Properties@ in the body
-- appear in the same order as the correspondingly-named @-- *@ sections in the
-- operations part of the body (one level shallower). Sections with no
-- operations counterpart (e.g. @-- ** Generators@, @-- ** Internal helpers@)
-- are silently skipped.
checkPropertiesMatchOps :: FilePath -> Text -> Assertion
checkPropertiesMatchOps f src = do
  let opsSecs   = opsSections src          -- "Construction", "Queries", …
      propsSecs  = propsSections src        -- "Construction", "Queries", …
  case firstOutOfOrder propsSecs opsSecs of
    Nothing     -> pure ()
    Just (a, b) -> assertFailure $ T.unpack $
      "In " <> T.pack f <> ": Properties subsection '" <> a
      <> "' comes before '" <> b
      <> "' but the corresponding operations section comes after it"

-- | Section names (no @-- *@ prefix) of real @-- *@ headers in the operations
-- body (before @-- * Properties@), excluding "Internal helpers"/"Definitions".
opsSections :: Text -> [Text]
opsSections src =
  [ secName l
  | (prev, l) <- zip ls (drop 1 ls)
  , "-- ---" `T.isPrefixOf` prev
  , "-- * "  `T.isPrefixOf` l
  , secName l `notElem` ["Internal helpers", "Definitions"]
  ]
  where
    ls = takeWhile (\l -> not ("-- * Generators" `T.isPrefixOf` l)
                       && not ("-- * Properties" `T.isPrefixOf` l))
                   (bodyLines src)
    secName = T.strip . T.drop 4

-- | Section names (no @-- **@ prefix) of @-- **@ headers inside
-- @-- * Properties@ in the body.
propsSections :: Text -> [Text]
propsSections src =
  [ T.strip (T.drop 5 l)
  | (prev, l) <- zip ls (drop 1 ls)
  , "-- ---" `T.isPrefixOf` prev
  , "-- ** "  `T.isPrefixOf` l
  , T.strip (T.drop 5 l) `notElem` ["Internal helpers", "Definitions", "Helpers"]
  ]
  where
    ls = dropWhile (not . ("-- * Properties" `T.isPrefixOf`)) (bodyLines src)

-- | Number of leading @*@ characters after @"-- "@ in a section header.
secDepth :: Text -> Int
secDepth = T.length . T.takeWhile (== '*') . T.drop 3

-- | Given a list of items in "declared order" and a list in "definition order",
-- return the first adjacent pair @(a, b)@ where @a@ is declared before @b@ but
-- defined after it. Items not found in the definition list are ignored.
firstOutOfOrder :: [Text] -> [Text] -> Maybe (Text, Text)
firstOutOfOrder declared defined =
  let defPos      = zip defined [0 :: Int ..]
      withPos     = [ (nm, p) | nm <- declared, Just p <- [lookup nm defPos] ]
  in  case [ (a, b)
           | (a, pa) : rest <- tails withPos
           , (b, pb)        <- take 1 rest
           , pa > pb
           ] of
        (pair : _) -> Just pair
        []         -> Nothing

-- | The lines of @src@ between @module@ and @) where@ (the export list).
exportListLines :: Text -> [Text]
exportListLines src =
  takeWhile (not . (") where" `T.isPrefixOf`) . T.stripStart) $
  drop 1 $
  dropWhile (not . ("module " `T.isPrefixOf`)) (T.lines src)

-- | The lines of @src@ after @) where@ (the module body).
bodyLines :: Text -> [Text]
bodyLines src =
  drop 1 $
  dropWhile (not . (") where" `T.isPrefixOf`) . T.stripStart) (T.lines src)

-- | Extract exported names from the module header, in source order.
-- Lines of the form @, <ident>@ are entries; comment lines and blank lines
-- are skipped.
extractExports :: Text -> [Text]
extractExports src =
  [ nm
  | l <- exportListLines src
  , Just nm <- [exportName l]
  ]
  where
    exportName l =
      case T.stripStart l of
        t | Just t' <- T.stripPrefix ", " t
          -> let nm = T.takeWhile isIdentChar t'
             in if T.null nm then Nothing else Just nm
        _ -> Nothing

-- | Extract all @-- *@-family section headers from the export list, stripping
-- leading whitespace. The @*@ count is preserved so @-- *@, @-- **@, and
-- @-- ***@ remain distinct.
extractExportSections :: Text -> [Text]
extractExportSections src =
  [ T.stripStart l
  | l <- exportListLines src
  , "-- *" `T.isPrefixOf` T.stripStart l
  ]

-- | Extract real @-- *@-family section headers from the file body, in order.
-- A real header is a @-- *@ line immediately preceded by a @-- ---@ separator.
-- "Internal helpers" and "Definitions" subsections appear in the operations
-- half of the file and have no export-list counterpart; they are excluded.
extractBodySections :: Text -> [Text]
extractBodySections src =
  [ l
  | (prev, l) <- zip ls (drop 1 ls)
  , "-- ---" `T.isPrefixOf` prev
  , "-- *"   `T.isPrefixOf` l
  , not (secName l `elem` ["Internal helpers", "Definitions"])
  ]
  where
    ls = bodyLines src
    secName = T.strip . T.dropWhile (== '*') . T.drop 3

-- | Extract top-level definition names from a Haskell source file, in order.
-- Only the first occurrence of each name is kept (multi-equation definitions).
extractDefs :: Text -> [Text]
extractDefs src = dedupe $ concatMap defName (bodyLines src)
  where
    defName l
      | T.null l                           = []
      | isIndented l                       = []
      | "--" `T.isPrefixOf` T.stripStart l = []
      | otherwise =
          let nm = T.takeWhile isIdentChar l
          in if T.null nm then [] else [nm]
    isIndented l = case T.uncons l of
      Just (c, _) -> c == ' ' || c == '\t'
      Nothing     -> False
    dedupe = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

------------------------------------------------------------------------
-- Source extraction

-- | Extract names of top-level @Property@-returning predicates from a Haskell
-- source file.
extractHsPredicates :: Text -> [Text]
extractHsPredicates = extractPredicates "::"

-- | Extract names of top-level @Property@-returning predicates from a Cryptol
-- source file.
extractCryPredicates :: Text -> [Text]
extractCryPredicates = extractPredicates ":"

-- | Extract all top-level predicates whose return type is @Property@ from a
-- source file. The signature operator (@\"::\"@ for Haskell, @\":\"@ for
-- Cryptol) is passed in. Multi-line signatures (where the body continues on
-- indented lines) are collapsed before matching the trailing return type.
extractPredicates :: Text -> Text -> [Text]
extractPredicates sigOp src =
  Set.toAscList . Set.fromList $ go (T.lines src)
  where
    go [] = []
    go (l : rest)
      | Just (nm, restOfLine) <- splitSig sigOp l
      , let (continuation, rest') = span isContinuation rest
            collapsed = T.unwords (restOfLine : map T.stripStart continuation)
      , trailingTokenIs "Property" collapsed
      = nm : go rest'
      | otherwise = go rest

    -- A continuation of a signature: indented and non-blank.
    isContinuation l = case T.uncons l of
      Just (c, _) -> c == ' ' || c == '\t'
      Nothing     -> False

-- | If @line@ begins with an identifier followed by @sigOp@ (e.g.
-- @\"::\"@), return the identifier and the rest of the line after the
-- operator. Otherwise 'Nothing'.
splitSig :: Text -> Text -> Maybe (Text, Text)
splitSig sigOp line
  | not (T.null nm)
  , Just rest' <- T.stripPrefix sigOp (T.stripStart rest)
  = Just (nm, rest')
  | otherwise = Nothing
  where
    (nm, rest) = T.span isIdentChar line

-- | True if the last whitespace-separated token of @s@ equals @tok@.
trailingTokenIs :: Text -> Text -> Bool
trailingTokenIs tok s = case reverse (T.words s) of
  []      -> False
  (w : _) -> w == tok

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_' || c == '\''
