module Main where

import ANSI
import Bwd
import Parse
import Actor
import Elaboration.Pretty()
import Machine
import Pretty
import Term.Base
import Main.Options
import Command

main :: IO ()
main = do
  opts <- getOptions
  txt <- readFile (filename opts)
  let ccs = parse pfile txt
  acs <- case elaborate ccs of
           Left err -> error $ withANSI [ SetColour Background Red ] "Error" ++ "\n" ++ pretty err
           Right acs -> pure acs
  -- putStrLn $ unsafeEvalDisplay initNaming $ collapse <$> traverse display acs
  let p = Process [] B0 initRoot (initEnv B0) initStore Win ""
  let res@(Process _ fs _ env sto Win _) = run opts p acs
  -- putStrLn $ display initNaming res
  dmesg "" res `seq` pure ()
