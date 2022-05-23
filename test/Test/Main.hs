module Main where

import Control.Monad

import Data.List ((\\))

import System.Directory
import System.FilePath

import Test.Tasty (TestTree,testGroup)
import Test.Tasty.Silver
import Test.Tasty.Silver.Interactive

data TestConfig = TestConfig
  { name      :: String
  , extension :: String
  , goldenExt :: String
  , folder    :: FilePath
  , excluded  :: [FilePath]
  }

main :: IO ()
main = defaultMain . testGroup "TypOS" =<< sequence
  [ typosExamples
  , typosTests
  , paperTYPES
  ]

paperTYPES :: IO TestTree
paperTYPES = do
  let name      = "TYPES paper"
  let extension = ".act"
  let goldenExt = ".gold"
  let folder    = "papers/2022-TYPES"
  let excluded  = []
  ioTests TestConfig{..}

typosExamples :: IO TestTree
typosExamples = do
  let name      = "Examples"
  let extension = ".act"
  let goldenExt = ".gold"
  let folder    = "examples"
  let excluded  = []
  ioTests TestConfig{..}


typosTests :: IO TestTree
typosTests = do
  let name      = "Tests"
  let extension = ".act"
  let goldenExt = ".gold"
  let folder    = "test"
  let excluded  = []
  ioTests TestConfig{..}


ioTests :: TestConfig -> IO TestTree
ioTests TestConfig{..} = testGroup name <$> do
  files <- findByExtension [extension] folder
  forM (files \\ ((folder </>) <$> excluded)) $ \ file -> do
    let dir  = takeDirectory file
    let name = takeBaseName file
    let gold = dir </> "golden" </> addExtension name goldenExt
    let flgs = dir </> addExtension name "flags"
    b <- doesFileExist flgs
    flags <- if b then words <$> readFile flgs else pure ["-q", "--no-colour"]
    pure $ goldenVsProg name gold "typos" (flags ++ [file]) ""
