module Main where

import Data.Foldable

import Bwd
import Parse
import Term
import Thin

shitMeta :: String -> Meta
shitMeta s = Meta [("user",0),(s,0)]

terms :: String -> [Term]
terms s = case parser (pspc *> ptm) B0 s of
  [(t,s)] -> (fmap shitMeta $^ t):(terms s)
  _ -> (error $ "syntax error: " ++ s) `seq` []

main :: IO ()
main = do
  s <- getContents
  let ts = terms s
  for_ ts $ \ t ->
    putStrLn (display' initNaming t)
