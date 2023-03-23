module Main where

import Control.Monad

import Data.List ((\\), isPrefixOf)

import System.Directory
import System.FilePath

import Test.Tasty (TestTree,testGroup)
import Test.Tasty.Silver
import Test.Tasty.Silver.Interactive

data TestConfig = TestConfig
  { name         :: String
  , extension    :: String
  , goldenExt    :: String
  , goldenDir    :: String
  , folder       :: FilePath
  , excluded     :: [FilePath]
  , excludedDirs :: [FilePath]
  }

main :: IO ()
main = defaultMain . testGroup "TypOS" =<< sequence
  [ typosExamples
  , typosTests
  , markdown
  -- , paperTYPES -- using an old version of the language
  ]

paperTYPES :: IO TestTree
paperTYPES = do
  let name      = "TYPES paper"
  let extension = ".act"
  let goldenExt = ".gold"
  let folder    = "papers/2022-TYPES"
  let goldenDir = folder </> "golden"
  let excluded  = []
  let excludedDirs = []
  ioTests TestConfig{..}

markdown :: IO TestTree
markdown = do
  let name      = "Markdown"
  let extension = ".md"
  let goldenExt = ".gold"
  let folder    = "."
  let goldenDir = "examples" </> "golden"
  let excluded  = ["TODO.md"]
  let excludedDirs = ["dist/", "dist-newstyle/", "build/"]
  ioTests TestConfig{..}


typosExamples :: IO TestTree
typosExamples = do
  let name      = "Examples"
  let extension = ".act"
  let goldenExt = ".gold"
  let folder    = "examples"
  let goldenDir = folder </> "golden"
  let excluded  = []
  let excludedDirs = []
  ioTests TestConfig{..}


typosTests :: IO TestTree
typosTests = do
  let name      = "Tests"
  let extension = ".act"
  let goldenExt = ".gold"
  let folder    = "test"
  let goldenDir = folder </> "golden"
  let excluded  = []
  let excludedDirs = []
  ioTests TestConfig{..}


ioTests :: TestConfig -> IO TestTree
ioTests TestConfig{..} = testGroup name <$> do
  files <- map normalise <$> findByExtension [extension] folder
  let excludedFiles = (normalise . (folder </>) <$> excluded)
  forM (filter (\ f -> not (any (`isPrefixOf` f) excludedDirs)) $ files \\ excludedFiles) $ \ file -> do
    let dir  = takeDirectory file
    let name = takeBaseName file
    let gold = goldenDir </> addExtension name goldenExt
    let flgs = dir </> addExtension name "flags"
    b <- doesFileExist flgs
    flags <- if b then words <$> readFile flgs else pure ["-q", "--no-colour", "--wAll"]
    putStrLn file
    pure $ goldenVsProg name gold "typos" (flags ++ [file]) ""
