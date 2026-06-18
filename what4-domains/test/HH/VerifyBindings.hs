{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module VerifyBindings where

import           Data.List (intercalate)
import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog.Alt
import qualified What4.Domains.Verification as V


verifyGenerators :: V.GenEnv Gen
verifyGenerators = V.GenEnv { V.genChooseBool = Gen.bool
                            , V.genChooseInteger = \r -> Gen.integral (uncurry Range.linear r)
                            , V.genChooseInt = \r -> Gen.int (uncurry Range.linear r)
                            , V.genGetSize = Gen.sized (\s -> return $ unSize s)
                            }


genTest :: String -> V.Gen V.Property -> TestTree
genTest nm p = testProperty nm $ property $ do
  (prop, draws) <- forAllWith (formatDraws . snd) (V.toNativeProperty verifyGenerators p)
  mkProp prop
  where mkProp (V.BoolProperty b) = test $ assert b
        mkProp (V.AssumptionProp a) = if (V.preCondition a) then (mkProp $ V.assumedProp a) else discard

-- | Like 'genTest' but with a much lower test count, for expensive
-- exact-containment properties (@*Exact@\/@*Precise@) whose cost isn't a
-- hot-path concern. The lower count is honored because 'setTestOptions' only
-- bumps the test-limit /default/ up to 5000 (see there).
genTestFew :: String -> V.Gen V.Property -> TestTree
genTestFew nm p = localOption (HedgehogTestLimit (Just 250)) (genTest nm p)

formatDraws :: [String] -> String
formatDraws [] = "Counterexample: (no primitive draws)"
formatDraws draws =
  "Counterexample (primitive draws in order):\n  "
    ++ intercalate "\n  " (zipWith fmtOne [0 :: Int ..] draws)
  where fmtOne i s = "drawn[" ++ show i ++ "] = " ++ s


setTestOptions :: TestTree -> TestTree
setTestOptions =
  -- some tests discard a lot of values based on preconditions;
  -- this helps prevent those tests from failing for insufficent coverage
  localOption (HedgehogDiscardLimit (Just 500000)) .

  -- Run 5000 tests by default, but honor an explicit per-test count (e.g. a
  -- 'localOption' on an expensive property): only bump the test-limit /default/
  -- (100, or unset) up to 5000, leaving any value a test set for itself untouched.
  adjustOption (\(HedgehogTestLimit x) ->
                  HedgehogTestLimit (if x == Just 100 || x == Nothing then Just 5000 else x))
