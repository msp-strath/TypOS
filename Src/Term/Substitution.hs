{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
module Term.Substitution where

import Bwd
import Hide
import Thin
import Term.Base hiding (expand)

-- import Debug.Trace
track = const id
-- track = trace

data OrdWit
  = LtBy Int -- positive
  | GeBy Int -- non-negative
  deriving Show

euclid :: Int -> Int -> OrdWit
euclid x y = let d = x - y in case d < 0 of
  True  -> LtBy (negate d)
  False -> GeBy d

(//^) :: Show m => CdB (Tm m) -> CdB (Sbst m) -> CdB (Tm m)
tth@(CdB t th) //^ sgph@(CdB sg ph) =
   track "\n" $
   track ("Term: " ++ show tth) $
   track ("Subst: " ++ show sgph) $
   case sbstSel th sg of
     CdB sg ps ->
       let res = CdB (t // sg) (ps <^> ph) in
       track ("Result: " ++ show res) $
       track "\n" $
       res

(//) :: Tm m -> Sbst m -> Tm m
t // (S0 :^^ _) = t
V // (ST (_ :<>: CdB (_ := t) _) :^^ 0) = t
P (CdB tl thl :<>: CdB tr thr) // sg =
  P (CdB (tl // sgl) phl :<>: CdB (tr // sgr) phr) where
  CdB sgl phl = sbstSel thl sg
  CdB sgr phr = sbstSel thr sg
((x := b) :. t) // (sg :^^ w) = (x := b) :. (t // (sg :^^ if b then w+1 else w))
(m :$ rh) // sg = m :$ (rh /// sg)

(///) :: Sbst m -> Sbst m -> Sbst m
(S0 :^^ _) /// sg = sg
rh /// (S0 :^^ _) = rh
(rh :^^ v) /// (sg :^^ w) =
  case euclid w v of
    LtBy d -> case sg of
      ST (CdB sg phl :<>: t) ->
        (ST (CdB ((rh :^^ (d-1)) /// sg) phl :<>: t) :^^ w)
      {-
          -------  ;  -------
             w           w
          -------     -------
          -------     ----> t
           d > 0         sg
          -------
             rh
      -}
    GeBy d -> case rh of
      ST (CdB rh thl :<>: CdB (x := s) thr) -> let
        CdB sgl phl = sbstSel thl (sg :^^ d)
        CdB sgr phr = sbstSel thr (sg :^^ d)
        in (ST (CdB (rh /// sgl) phl :<>: CdB (x := (s // sgr)) phr) :^^ v)
      {-
        -------  ;  -------
           v           v
        -------     -------
        ----> s     -------
           rh          d
                    -------
                       sg
      -}

expand :: Sbst m           -- ga ---> de0
       -> Th               -- de0 <= de
       -> Bwd (CdB (Tm m)) -- [Term de]
expand (S0 :^^ 0) th = B0
expand (ST (CdB sg th' :<>: (CdB (hi := tm) ph)) :^^ 0) th = expand sg (th' *^ th) :< (CdB tm ph) *^ th
expand (sg :^^ n) th = expand (sg :^^ (n - 1)) (th -? False) :< var (DB 0) (weeEnd th) *^ th
