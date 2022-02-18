{-# LANGUAGE TypeSynonymInstances #-}

module Term.Display where

import Data.List

import Bwd
import Thin
import Hide
import Term

import Display

instance Show m => Display (Tm m) where
  display (B0 :< x, _, _) V = x
  display (B0, _, _)    (A a) = case a of
    "" -> "[]"
    _  -> '\'' : a
  display na (P (s :<>: t)) =
    "[" ++ pdisplay na s ++ displayCdr' na t ++ "]"
  display na ((Hide x := b) :. t) = "\\" ++ case b of
    False -> "_." ++ display na t
    True  -> let y = freshen x na in
      y ++ "." ++ display (nameOn na y) t
  display na (m :$ sg) = display na sg ++ "?" ++ show m
  display na tm = error $ show na ++ "\n" ++ show tm

  pdisplay na t = case t of
    A{} -> display na t
    P{} -> display na t
    _ -> pdisplayDFT na t

instance Show m => Display (CdB (Tm m)) where
  display  na@(_, ph, _) (CdB (t', th)) = display  (nameSel th na) t'
  pdisplay na@(_, ph, _) (CdB (t', th)) = pdisplay (nameSel th na) t'

displayCdr :: Show m => Naming -> Tm m -> String
displayCdr (B0, _, _) (A "") = ""
displayCdr na (P (s :<>: t)) = " " ++ pdisplay na s ++ displayCdr' na t
displayCdr na t = "|" ++ display na t

displayCdr' :: Show m => Naming -> CdB (Tm m) -> String
displayCdr' na t@(CdB (t', th)) = displayCdr (nameSel th na) t'

instance Show m => Display (Sbst m) where
  display na@(_, th, _) sg = case displaySg na sg of
    [] -> []
    sg' -> "{" ++ intercalate "," sg' ++ "}"

   where

     displaySg :: Show m => Naming -> Sbst m -> [String]
     displaySg (_, th, _) (S0 :^^ _)
       | th == ones (bigEnd th) = []
     displaySg na (ST (CdB (sg, th) :<>: CdB ((Hide x := t), ph)) :^^ 0) =
       (x ++ "=" ++ display na (CdB (t, ph))) :
       displaySg (nameSel th na) sg
     displaySg (xz, th, yz :< y) (sg :^^ w) = case thun th of
       (th, False) ->
         (y ++ "*") : displaySg (xz, th, yz) (sg :^^ w)
       (th, True) ->
         case xz of
           xz :< x ->
             x : displaySg (xz, th, yz) (sg :^^ (w - 1))
