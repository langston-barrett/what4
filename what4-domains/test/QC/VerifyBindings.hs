{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module VerifyBindings where

import           Data.List (intercalate)
import           Test.Tasty
import           Test.Tasty.QuickCheck
import qualified What4.Domains.Verification as V


instance Testable V.Property where
  property = \case
    V.BoolProperty b -> property b
    V.AssumptionProp a -> (V.preCondition a) ==> (V.assumedProp a)

verifyGenerators :: V.GenEnv Gen
verifyGenerators = V.GenEnv { V.genChooseBool = elements [ True, False ]
                            , V.genChooseInteger = \r -> choose r
                            , V.genChooseInt = \r -> choose r
                            , V.genGetSize = getSize
                            }


genTest :: String -> V.Gen V.Property -> TestTree
genTest nm p = testProperty nm $ do
  (prop, draws) <- V.toNativeProperty verifyGenerators p
  pure (counterexample (formatDraws draws) prop)

-- | Like 'genTest' but with a much lower QuickCheck count, for expensive
-- exact-containment properties (@*Exact@\/@*Precise@) whose cost isn't a
-- hot-path concern. The lower count is honored because 'setTestOptions' only
-- bumps the QuickCheck /default/ up to 5000 (see there).
genTestFew :: String -> V.Gen V.Property -> TestTree
genTestFew nm p = localOption (QuickCheckTests 250) (genTest nm p)

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
  localOption (QuickCheckMaxRatio 1000) .

  -- Run 5000 tests by default, but honor an explicit per-test count (e.g. a
  -- 'localOption' on an expensive property): only bump the QuickCheck /default/
  -- (100) up to 5000, leaving any value a test set for itself untouched.
  adjustOption (\(QuickCheckTests x) ->
                  QuickCheckTests (if x == 100 then 5000 else x))
