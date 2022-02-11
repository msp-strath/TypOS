{-# LANGUAGE OverloadedStrings, StandaloneDeriving #-}

module Actor.Display where


import qualified Data.Map as Map

import Actor
import Bwd
import Display
import Hide
import Pattern
import Scope
import Term.Display()

instance Display PatVar where
  display na@(ns, _, _) = \case
    VarP n -> ns <! n

instance Display Env where
  display na (Env sc avs) =
    collapse $
    map (\ (av, (xs, t)) -> concat (show av : map (" " ++) xs ++ [" = ", display (foldl nameOn na xs) t])) (Map.toList avs)


instance Display MatchLabel where
  display _ (MatchLabel str) = maybe "" ('/' :) str

instance Display Actor where
  display na = \case
    a :|: b -> pdisplay na a ++ " | " ++ pdisplay na b
    Closure env a -> unwords ["Closure", display na env, pdisplay na a]
    Spawn jd ch a -> concat [jd, "@", show ch, ". ", display na a]
    Send ch tm a ->  concat [show ch, "!", pdisplay na tm, ". ", display na a]
    Recv ch av a -> concat [show ch, "?", show av, ". ", display na a]
    FreshMeta av a -> concat ["?", show av, ". ", pdisplay na a]
    Under (Scope (Hide x) a) -> concat ["\\", x, ". ", display (na `nameOn` x) a]
    Match lbl tm pts -> concat ["case", display initNaming lbl, " ", display na tm, " "
                               , collapse (BracesList (display na <$> pts))
                               ]
    Constrain s t -> unwords [pdisplay na s, "~", pdisplay na t]
    Extend (jd, ml, i, a) b ->
      concat [jd, display initNaming ml, " { ", pdisplay na i, " -> ", pdisplay na a, " }. "
             , pdisplay na b]
    Fail gr -> unwords ["#\"", gr, "\""]
    Win -> "Win"
    Print tm a -> unwords ["PRINT", pdisplay na tm, ". ", pdisplay na a]
    Break str a -> display na a

instance Display t => Display (PatF t, Actor) where
  display na (p, a) = display na p ++ " -> " ++ display na a
