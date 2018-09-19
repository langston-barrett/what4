-- | Command line interface to crucible-jvm
--
-- Currently this executable works as a simulator for Java classes.
-- It expects a static method "main" that takes no arguments and
-- returns an int result. It then executes the method and prints out
-- the result in hex.

-- TODO: set this up so we can make it run test cases

{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language FlexibleContexts #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Main where

import Data.String(fromString)
import qualified Data.Map as Map
import Control.Lens((^.))
import Control.Monad.ST
import Control.Monad
import Control.Monad.State.Strict

import Control.Exception(SomeException(..),displayException)
import Data.List

import System.Console.GetOpt
import System.IO
import System.Environment(getProgName,getArgs)
import System.FilePath(takeExtension,takeBaseName)
import System.FilePath(splitSearchPath)

import Data.Parameterized.Nonce(withIONonceGenerator)
import Data.Parameterized.Some(Some(..))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF

-- crucible/crucible
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(SomeCFG(..), AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle

import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.GlobalState
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Simulator.RegMap


-- crucible/what4
import What4.ProgramLoc
import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4

-- jvm-verifier
import qualified Language.JVM.Common as J
import qualified Language.JVM.Parser as J

-- crux
import qualified Crux.Language as Crux
import qualified Crux.CruxMain as Crux
import qualified Crux.Options  as Crux


import qualified Lang.JVM.Codebase as JCB

import           Lang.Crucible.JVM.Translation


-- executable

import System.Console.GetOpt


instance Crux.Language JVM where
  type LangError JVM = ()
  formatError _ = ""

  -- command line options specific to crux-jvm
  data LangOptions JVM =  JVMOptions
    { classPath        :: [FilePath]
      -- ^ where to look for the class path
    , jarList          :: [FilePath]
      -- ^ additional jars to use when evaluating jvm code
      -- this must include rt.jar from the JDK
      -- (The JDK_JAR environment variable can also be used to
      -- to specify this JAR).
    , mainMethod       :: String
    }

  defaultOptions =
    JVMOptions
    { classPath  = ["."]
    , jarList    = []
    , mainMethod = "main"
    }

  cmdLineOptions = [
    Option "c" ["classpath"]
    (ReqArg
     (\p opts -> opts { classPath = classPath opts ++ splitSearchPath p })
     "path"
    )
    Crux.pathDesc
    , Option "j" ["jars"]
    (ReqArg
     (\p opts -> opts { jarList = jarList opts ++ splitSearchPath p })
     "path"
    )
    Crux.pathDesc
    ,  Option "m" ["method"]
    (ReqArg
     (\p opts -> opts { mainMethod = p })
     "method name"
    )
    "Method to similate"
    ]

  envOptions   = [("JDK_JAR", \ p os -> os { jarList = p : jarList os })]
  ioOptions    = return 

  name = "jvm"
  validExtensions = [".java"]
  
  simulate (copts,opts) sym ext file = do
     let verbosity = Crux.simVerbose copts
     
     cb <- JCB.loadCodebase (jarList opts) (classPath opts)

     let cname = takeBaseName file
     let mname = mainMethod opts

     -- create a null array of strings for `args`
     -- TODO: figure out how to allocate an empty array
     let nullstr = RegEntry refRepr W4.Unassigned
     let regmap = RegMap (Ctx.Empty `Ctx.extend` nullstr)

     executeCrucibleJVM @UnitType cb verbosity sym
       ext cname mname regmap
       
  makeCounterExamples _opts _proved = return ()

    

-- | Entry point, parse command line opions
main :: IO ()
main = Crux.main [Crux.LangConf (Crux.defaultOptions @JVM)]
{-
     res <- executeCrucibleJVM @UnitType cb (simVerbose opts) sym
       personality cname mname regmap
-}

