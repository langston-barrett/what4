-----------------------------------------------------------------------
-- |
-- Module           : What4.Solver.Adapter
-- Description      : Defines the low-level interface between a particular
--                    solver and the SimpleBuilder family of backends.
-- Copyright        : (c) Galois, Inc 2015-2020
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
------------------------------------------------------------------------

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module What4.Solver.Adapter
  ( SolverAdapter(..)
  , defaultWriteSMTLIB2Features
  , defaultSolverAdapter
  , solverAdapterOptions
  , LogData(..)
  , logCallback
  , defaultLogData
  , smokeTest
  ) where

import qualified Control.Exception as X
import           Data.Bits
import           Data.IORef
import qualified Data.Map as Map
import qualified Data.Text as T
import           System.IO
import qualified Prettyprinter as PP


import           What4.BaseTypes
import           What4.Config
import           What4.Concrete
import           What4.Interface
import           What4.SatResult
import           What4.ProblemFeatures
import           What4.Expr.Builder
import           What4.Expr.GroundEval


-- | The main interface for interacting with a solver in an "offline" fashion,
--   which means that a new solver process is started for each query.
data SolverAdapter st =
  SolverAdapter
  { solver_adapter_name :: !String

    -- | Configuration options relevant to this solver adapter
  , solver_adapter_config_options
        :: ![ConfigDesc]

    -- | Operation to check the satisfiability of a formula.
    --   The final argument is a callback that calculates the ultimate result from
    --   a SatResult and operations for finding model values in the event of a SAT result.
    --   Note: the evaluation functions may cease to be avaliable after the
    --   callback completes, so any necessary information should be extracted from
    --   them before returning.
  , solver_adapter_check_sat
        :: !(forall t fs a.
           ExprBuilder t st fs
        -> LogData
        -> [BoolExpr t]
        -> (SatResult (GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a)
        -> IO a)

    -- | Write an SMTLib2 problem instance onto the given handle, incorporating
    --   any solver-specific tweaks appropriate to this solver
  , solver_adapter_write_smt2 :: !(forall t fs . ExprBuilder t st fs -> Handle -> [BoolExpr t] -> IO ())
  }

-- | A collection of operations for producing output from solvers.
--   Solvers can produce messages at varying verbosity levels that
--   might be appropriate for user output by using the `logCallbackVerbose`
--   operation.  If a `logHandle` is provided, the entire interaction
--   sequence with the solver will be mirrored into that handle.
data LogData = LogData { logCallbackVerbose :: Int -> String -> IO ()
                       -- ^ takes a verbosity and a message to log
                       , logVerbosity :: Int
                       -- ^ the default verbosity; typical default is 2
                       , logReason :: String
                       -- ^ the reason for performing the operation
                       , logHandle :: Maybe Handle
                       -- ^ handle on which to mirror solver input/responses
                       }

logCallback :: LogData -> (String -> IO ())
logCallback logData = logCallbackVerbose logData (logVerbosity logData)

defaultLogData :: LogData
defaultLogData = LogData { logCallbackVerbose = \_ _ -> return ()
                         , logVerbosity = 2
                         , logReason = "defaultReason"
                         , logHandle = Nothing }

instance Show (SolverAdapter st) where
  show = solver_adapter_name
instance Eq (SolverAdapter st) where
  x == y = solver_adapter_name x == solver_adapter_name y
instance Ord (SolverAdapter st) where
  compare x y = compare (solver_adapter_name x) (solver_adapter_name y)

-- | Default featues to use for writing SMTLIB2 files.
defaultWriteSMTLIB2Features :: ProblemFeatures
defaultWriteSMTLIB2Features
  = useComputableReals
  .|. useIntegerArithmetic
  .|. useBitvectors
  .|. useQuantifiers
  .|. useSymbolicArrays

defaultSolverAdapter :: ConfigOption (BaseStringType Unicode)
defaultSolverAdapter = configOption (BaseStringRepr UnicodeRepr) "default_solver"


solverAdapterOptions ::
  [SolverAdapter st] ->
  IO ([ConfigDesc], IO (SolverAdapter st))
solverAdapterOptions [] = fail "No solver adapters specified!"
solverAdapterOptions xs@(def:_) =
  do ref <- newIORef def
     let opts = sty ref : concatMap solver_adapter_config_options xs
     return (opts, readIORef ref)

 where
 f ref x = (T.pack (solver_adapter_name x), atomicWriteIORef ref x >> return optOK)
 vals ref = Map.fromList (map (f ref) xs)
 sty ref = mkOpt defaultSolverAdapter
                 (listOptSty (vals ref))
                 (Just (PP.pretty "Indicates which solver to use for check-sat queries"))
                 (Just (ConcreteString (UnicodeLiteral (T.pack (solver_adapter_name def)))))

-- | Test the ability to interact with a solver by peforming a check-sat query
--   on a trivially unsatisfiable problem.
smokeTest :: ExprBuilder t st fs -> SolverAdapter st -> IO (Maybe X.SomeException)
smokeTest sym adpt = test `X.catch` (pure . Just)
  where
  test :: IO (Maybe X.SomeException)
  test =
    solver_adapter_check_sat adpt sym defaultLogData [falsePred sym] $ \case
      Unsat{} -> pure Nothing
      _ -> fail "Smoke test failed: expected UNSAT"
