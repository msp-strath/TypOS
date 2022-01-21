{-# LANGUAGE OverloadedStrings, StandaloneDeriving #-}

module Actor.Display where


import qualified Data.Map as Map

import Actor
import Bwd
import Display
import Term
import Term.Display()
import Pattern


instance Display PatVar where
  display na@(ns, _, _) = \case
    VarP n -> ns <! n

instance Display Env where
  display na (Env sc avs als) =
    collapse $
    map (\ (av, (xs, t)) -> concat (show (ActorVar av) : map (" " ++) xs ++ [" = ", display (foldl nameOn na xs) t])) (Map.toList avs)
    ++ map (\ (al, i) -> show (Alias al) ++ " = " ++ display na (var i sc :: Term)) (Map.toList als)

instance Display Actor where
  display na = \case
    a :|: b -> pdisplay na a ++ " :|: " ++ pdisplay na b
    Closure env a -> unwords ["Closure", display na env, pdisplay na a]
    Spawn jd ch a -> unwords ["Spawn", jd, show ch, pdisplay na a]
    Send ch tm a -> unwords ["Send", show ch, pdisplay initNaming tm, pdisplay na a]
    Recv ch av a -> unwords ["Recv", show ch, av, pdisplay na a]
    FreshMeta av a -> unwords ["FreshMeta", av, pdisplay na a]
    Under x a -> unwords ["Under", x, pdisplay na a]
    Match lbl tm pts -> unwords ["Match", lbl, pdisplay initNaming tm, collapse (display na <$> pts)]
    Constrain s t -> unwords ["Constrain", pdisplay initNaming s, pdisplay initNaming t]
    Extend (jd, ml, i, a) b ->
      unwords ["Extend", jd, ml, i, pdisplay na a, pdisplay na b]
    Fail gr -> unwords ["Fail", gr]
    Win -> "Win"
    Break str a -> display na a

instance Display t => Display (PatF t, Actor) where
  display na (p, a) = display na p ++ " -> " ++ display na a
