module Main where

import Data.Foldable

import Bwd
import Parse
import Term
import Thin
import Display
import Syntax
import Command

shitMeta :: String -> Meta
shitMeta s = Meta [("user",0),(s,0)]

terms :: String -> [Term]
terms s = case parser (pspc *> ptm <* pnl) B0 s of
  [(t,s)] -> (fmap shitMeta $^ t):(terms s)
  _ -> (error $ "Unparsed input: " ++ s) `seq` []

main :: IO ()
main = do
  s <- getContents
  let ts = terms s
  for_ ts $ \ t ->
    putStrLn (display' initNaming t)

{-
test = display' initNaming (fst (head (parser (pspc *> ptm) B0 (display' initNaming syntaxDesc)))) == display' initNaming syntaxDesc
-}
