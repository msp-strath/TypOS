{-# LANGUAGE
  FlexibleInstances,
  TypeSynonymInstances,
  LambdaCase,
  TupleSections,
  PatternGuards
  #-}

module Display where

import Data.List

import Bwd
import Thin
import Hide
import Term

-- uglyprinting

type Naming =
  ( Bwd String  -- what's in the support
  , Th          -- and how that was chosen from
  , Bwd String  -- what's in scope
  )

initNaming :: Naming
initNaming = (B0, ones 0, B0)

-- The point is that when we reach a metavariable,
-- we have to document its permitted dependencies.

nameSel :: Th -> Naming -> Naming
nameSel th (xz, ph, yz) = (th ?< xz, th <^> ph, yz)

nameOn :: Naming -> String -> Naming
nameOn (xz, th, yz) x = (xz :< x, th -? True, yz :< x)

freshen :: String -> Naming -> String
freshen x (xz, _, _) = head [y | y <- ys, all (y /=) xz] where
  ys = x : [x ++ show (i :: Integer) | i <- [0..]]

display :: Show m => Naming -> Tm m -> String
display (B0 :< x, _, _) V = x
display (B0, _, _)    (A a) = case a of
  "" -> "[]"
  _  -> '\'' : a
display na (P (s :<>: t)) =
  "[" ++ display' na s ++ displayCdr' na t ++ "]"
display na ((Hide x := b) :. t) = "\\" ++ case b of
  False -> "_." ++ display na t
  True  -> let y = freshen x na in
    y ++ "." ++ display (nameOn na y) t
display na (m :$ sg) = case displaySg na sg of
  [] -> "?" ++ show m
  sg' -> "{" ++ intercalate "," sg' ++ "}?" ++ show m

display' :: Show m => Naming -> CdB (Tm m) -> String
display' na t@(t', th) = case asList Just t of
  Just ts -> "'[" ++ intercalate " " (map (display' na) ts) ++ "]"
  Nothing -> display (nameSel th na) t'

displayCdr :: Show m => Naming -> Tm m -> String
displayCdr (B0, _, _) (A "") = ""
displayCdr na (P (s :<>: t)) =
  " " ++ display' na s ++ displayCdr' na t
displayCdr na t = "|" ++ display na t

displayCdr' :: Show m => Naming -> CdB (Tm m) -> String
displayCdr' na t@(t', th) = case asList Just t of
  Just ts -> "| '[" ++ intercalate " " (map (display' na) ts) ++ "]"
  Nothing -> displayCdr (nameSel th na) t'


displaySg :: Show m => Naming -> Sbst m -> [String]
displaySg (_, th, _) (S0 :^^ _)
  | th == ones (bigEnd th) = []
displaySg na (ST ((sg, th) :<>: ((Hide x := t), ph)) :^^ 0) =
  (x ++ "=" ++ display' na (t, ph)) :
  displaySg (nameSel th na) sg
displaySg (xz, th, yz :< y) (sg :^^ w) = case thun th of
  (th, False) ->
    (y ++ "*") : displaySg (xz, th, yz) (sg :^^ w)
  (th, True) ->
    case xz of
      xz :< x ->
        x : displaySg (xz, th, yz) (sg :^^ (w - 1))

displayCdB :: Show m => Naming -> CdB (Tm m) -> String
displayCdB nm (t, th) = "(" ++ display nm t ++ ", " ++ show th ++ ")"
