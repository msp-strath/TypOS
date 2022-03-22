module Main where

import Control.Monad

import Data.List ((\\))

import System.FilePath

import Test.Tasty (TestTree,testGroup)
import Test.Tasty.Silver
import Test.Tasty.Silver.Interactive

data TestConfig = TestConfig
  { name      :: String
  , extension :: String
  , goldenExt :: String
  , excluded  :: [FilePath]
  }

main :: IO ()
main = defaultMain . testGroup "Tests" =<< sequence
  [ typosTests
  ]

typosTests :: IO TestTree
typosTests = do
  let name      = "TypOS"
  let extension = ".act"
  let goldenExt = ".gold"
  let excluded = ["./examples/mltt_krivine.act"]
  ioTests TestConfig{..}

ioTests :: TestConfig -> IO TestTree
ioTests TestConfig{..} = testGroup name <$> do
  files <- findByExtension [extension] "."
  forM (files \\ excluded) $ \ file -> do
    let dir  = takeDirectory file
    let name = takeBaseName file
    let gold = dir </> "golden" </> addExtension name goldenExt
    pure $ goldenVsProg name gold "typos" [file] ""
