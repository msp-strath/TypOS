{-# LANGUAGE
  TypeSynonymInstances,
  PatternGuards
  #-}

module Display where

import Data.List

import Bwd
import Thin
import Hide
import Term
import ANSI

-- uglyprinting

type Naming =
  ( Bwd String  -- what's in the support
  , Th          -- and how that was chosen from
  , Bwd String  -- what's in scope
  )

initNaming :: Naming
initNaming = (B0, ones 0, B0)

fromScope :: Int -> Naming
fromScope n = (ns, ones n, ns) where
  ns = B0 <>< map (("x" ++) . show) [0..n-1]

-- The point is that when we reach a metavariable,
-- we have to document its permitted dependencies.

nameSel :: Th -> Naming -> Naming
nameSel th (xz, ph, yz) = (th ?< xz, th <^> ph, yz)

nameOn :: Naming -> String -> Naming
nameOn (xz, th, yz) x = (xz :< x, th -? True, yz :< x)

freshen :: String -> Naming -> String
freshen x (xz, _, _) = head [y | y <- ys, all (y /=) xz] where
  ys = x : [x ++ show (i :: Integer) | i <- [0..]]

pdisplayDFT :: Display t => Naming -> t -> String
pdisplayDFT na t =
  let t' = display na t in
  if ' ' `elem` t' then concat ["(", t', ")"] else t'

class Display t where
  display :: Naming -> t -> String

  pdisplay :: Naming -> t -> String
  pdisplay = pdisplayDFT

instance Display () where
  display _ _ = "()"

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
  display na t@(t', th) = case asList Just t of
    Just ts -> "'[" ++ intercalate " " (map (display na) ts) ++ "]"
    Nothing -> display (nameSel th na) t'

  pdisplay na t@(t', th) = case asList Just t of
    Just ts -> "'[" ++ intercalate " " (map (display na) ts) ++ "]"
    Nothing -> pdisplay (nameSel th na) t'

-- TODO: fancy printing for lists
instance Display t => Display (PatF t) where
  display na = \case
    VP n -> display na n
    AP ""  -> "[]"
    AP str -> "'" ++ str
    PP p q -> "[" ++ pdisplay na p ++ displayPatCdr na q ++ "]"
    BP (Hide x) p -> "\\" ++ x ++ "." ++ display (na `nameOn` x) p
    MP m th -> m

  pdisplay na p = case p of
    AP{} -> display na p
    PP{} -> display na p
    _ -> pdisplayDFT na p

displayPatCdr :: Display t => Naming -> PatF t -> String
displayPatCdr na (AP "") = ""
displayPatCdr na (PP p q) = " " ++ pdisplay na p ++ displayPatCdr na q
displayPatCdr na t = "|" ++ display na t

displayCdr :: Show m => Naming -> Tm m -> String
displayCdr (B0, _, _) (A "") = ""
displayCdr na (P (s :<>: t)) = " " ++ pdisplay na s ++ displayCdr' na t
displayCdr na t = "|" ++ display na t

displayCdr' :: Show m => Naming -> CdB (Tm m) -> String
displayCdr' na t@(t', th) = case asList Just t of
  Just ts -> "| '[" ++ intercalate " " (map (display na) ts) ++ "]"
  Nothing -> displayCdr (nameSel th na) t'


instance Show m => Display (Sbst m) where
  display na sg = case displaySg na sg of
    [] -> []
    sg' -> "{" ++ intercalate "," sg' ++ "}"

   where

     displaySg :: Show m => Naming -> Sbst m -> [String]
     displaySg (_, th, _) (S0 :^^ _)
       | th == ones (bigEnd th) = []
     displaySg na (ST ((sg, th) :<>: ((Hide x := t), ph)) :^^ 0) =
       (x ++ "=" ++ display na (t, ph)) :
       displaySg (nameSel th na) sg
     displaySg (xz, th, yz :< y) (sg :^^ w) = case thun th of
       (th, False) ->
         (y ++ "*") : displaySg (xz, th, yz) (sg :^^ w)
       (th, True) ->
         case xz of
           xz :< x ->
             x : displaySg (xz, th, yz) (sg :^^ (w - 1))

-- displayCdB :: Show m => Naming -> CdB (Tm m) -> String
-- displayCdB nm (t, th) = "(" ++ display nm t ++ ", " ++ show th ++ ")"

instance Display Int where
  display _ i = show i

class Collapse t where
  collapse :: t String -> String

instance Collapse Bwd where
  collapse strs = "[<" ++ intercalate ", " (strs <>> []) ++ "]"

instance Collapse [] where
  collapse strs = "[" ++ intercalate ", " strs ++ "]"

instance Collapse Cursor where
  collapse (lstrs :<+>: rstrs) =
    unwords [ collapse lstrs
            , withANSI [SetColour Foreground Red, SetWeight Bold] ":<+>:"
            , collapse rstrs
            ]
