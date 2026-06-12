{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module W2SMT2
  ( main
  ) where

import Data.Parameterized.Nonce qualified as Nonce
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text.IO
import Data.Text.Lazy qualified as Text.Lazy
import Data.Text.Lazy.Builder qualified as Builder
import System.Environment qualified as Env
import System.Exit qualified as Exit
import System.IO qualified as IO
import System.IO.Temp qualified as Temp
import System.Process qualified as Proc

import What4.Interface qualified as WI
import What4.Protocol.SMTLib2.Syntax qualified as SMT2
import What4.SatResult qualified as WSR

import Who2.Builder qualified as W2
import Who2.Protocol.SMTLib2 qualified as W2SMT

import W4SMT2.Exec qualified as Exec
import W4SMT2.Parser qualified as Parser
import W4SMT2.Solve qualified as Solve

validSolvers :: [String]
validSolvers = ["bitwuzla", "cvc5", "yices", "z3"]

parseArgs :: IO (Maybe String, Maybe FilePath)
parseArgs = do
  args <- Env.getArgs
  case args of
    [] -> return (Nothing, Nothing)
    [arg] -> if arg `elem` validSolvers
             then return (Just arg, Nothing)
             else return (Nothing, Just arg)
    [solver, file] -> if solver `elem` validSolvers
                      then return (Just solver, Just file)
                      else usage
    _ -> usage
  where
    usage = do
      IO.hPutStrLn IO.stderr "Usage: w2smt2 [SOLVER] [FILE]"
      IO.hPutStrLn IO.stderr "  SOLVER: bitwuzla, cvc5, yices, or z3 (optional)"
      IO.hPutStrLn IO.stderr "  FILE: Path to SMT-LIB2 file (optional, reads from stdin if not provided)"
      Exit.exitFailure

main :: IO ()
main = do
  (maybeSolver, maybeFilePath) <- parseArgs
  input <- case maybeFilePath of
    Nothing -> Text.IO.getContents
    Just path -> Text.IO.readFile path
  let ?logStderr = Text.IO.hPutStrLn IO.stderr
  execResult <- case maybeSolver of
    Nothing ->
      Nonce.withIONonceGenerator $ \gen -> do
        sym <- W2.newBuilder gen
        Solve.solve sym input
    Just solverName ->
      -- Build via Who2 (so strides simplification runs), then re-emit each
      -- assertion as SMT-LIB2 and shell out to the external solver.
      Nonce.withIONonceGenerator $ \gen -> do
        sym <- W2.newBuilder gen
        sexps <- Parser.parseSExps input
        Exec.execCommands sym Exec.initState (Just (externalCallback solverName)) sexps
  mapM_ outputResult (Exec.erResults execResult)
  where
    outputResult result = case result of
      WSR.Sat () -> putStrLn "sat"
      WSR.Unsat () -> putStrLn "unsat"
      WSR.Unknown -> putStrLn "unknown"

-- | Callback invoked by 'Exec.execCommands' at each @check-sat@. Serializes
-- the accumulated assertions through Who2's SMT-LIB2 protocol and runs the
-- query against the named external solver via a temp file.
externalCallback ::
  forall t.
  String ->
  W2.Builder t ->
  [WI.Pred (W2.Builder t)] ->
  IO (WSR.SatResult () ())
externalCallback solverName _sym preds = do
  (decls, terms) <- W2SMT.mkAssertions preds
  let renderAssertion t =
        let body = Text.Lazy.toStrict (Builder.toLazyText (SMT2.renderTerm t))
        in "(assert " <> body <> ")"
  let query = Text.unlines $
        [ "(set-logic QF_BV)" ]
        ++ decls
        ++ map renderAssertion terms
        ++ [ "(check-sat)" ]
  runExternalSolver solverName query

-- | Hand a fully-formed SMT-LIB2 query to an external solver, parse the first
-- @sat@/@unsat@/@unknown@ line.
runExternalSolver :: String -> Text -> IO (WSR.SatResult () ())
runExternalSolver solverName query = do
  -- If W2SMT2_DUMP_QUERY is set, write the rewritten query there for inspection.
  dumpPath <- Env.lookupEnv "W2SMT2_DUMP_QUERY"
  case dumpPath of
    Just p  -> Text.IO.writeFile p query
    Nothing -> pure ()
  Temp.withSystemTempFile "w2smt2.smt2" $ \tmpPath h -> do
    Text.IO.hPutStr h query
    IO.hClose h
    let (cmd, args) = getSolverCommand solverName tmpPath
    (_, stdout, _) <- Proc.readProcessWithExitCode cmd args ""
    return $ parseExternalSolverOutput stdout

getSolverCommand :: String -> FilePath -> (String, [String])
getSolverCommand solverName path = case solverName of
  "z3" -> ("z3", [path])
  "yices" -> ("yices-smt2", [path])
  "cvc5" -> ("cvc5", [path])
  "bitwuzla" -> ("bitwuzla", [path])
  _ -> error $ "Unknown solver: " ++ solverName

-- | Pick the first sat/unsat/unknown line from solver output. Defaults to
-- @Unknown@ if none of those appear.
parseExternalSolverOutput :: String -> WSR.SatResult () ()
parseExternalSolverOutput output =
  case [ trimmed
       | line <- lines output
       , let trimmed = Text.strip (Text.pack line)
       , trimmed `elem` ["sat", "unsat", "unknown"]
       ] of
    ("sat":_)     -> WSR.Sat ()
    ("unsat":_)   -> WSR.Unsat ()
    ("unknown":_) -> WSR.Unknown
    _             -> WSR.Unknown
