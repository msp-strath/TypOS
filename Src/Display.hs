{-# LANGUAGE
  TypeSynonymInstances,
  PatternGuards
  #-}

module Display where

import Data.List

import Bwd
import Thin
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
