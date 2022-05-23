module Syntax.Debug where

import Syntax
import Data.Maybe (fromJust)
import qualified Data.Map as Map
import Display (display, unsafeEvalDisplay)
import Machine.Display()
import Unelaboration (initNaming)

printIt = putStrLn $ unlines
  [ show validateIt
  , "==="
  , show (unsafeEvalDisplay initNaming $ display (syntaxDesc ["Syntax"]))
  , "==="
  , show (unsafeEvalDisplay initNaming $ display $ Syntax.contract (fromJust (Syntax.expand (Map.singleton "Syntax" (syntaxDesc ["Syntax"])) (syntaxDesc ["Syntax"]))))]

{-
['EnumOrTag
  ['Nil 'Atom 'Wildcard 'Syntax]
  [['AtomBar ['Fix \at. ['NilOrCons 'Atom at]]]
   ['Cons 'Syntax 'Syntax]
   ['NilOrCons 'Syntax 'Syntax]
   ['Bind ['EnumOrTag ['Syntax] []] 'Syntax]
   ['EnumOrTag ['Fix \at. ['NilOrCons 'Atom at]]
               ['Fix \cell. ['NilOrCons ['Cons 'Atom ['Fix \rec. ['NilOrCons 'Syntax rec]]] cell]]]
   ['Enum ['Fix \at. ['NilOrCons 'Atom at]]]
   ['Tag ['Fix \cell. ['NilOrCons ['Cons 'Atom ['Fix \rec. ['NilOrCons 'Syntax rec]]] cell]]]
   ['Fix ['Bind 'Syntax 'Syntax]]]]
-}
