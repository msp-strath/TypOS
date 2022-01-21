module Term.Substitution where

import Thin
import Term.Base

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
tth@(t, th) //^ sgph@(sg, ph) =
   track "\n" $
   track ("Term: " ++ show tth) $
   track ("Subst: " ++ show sgph) $
   case sbstSel th sg of
     (sg, ps) -> let res = (t // sg, ps <^> ph) in
                 track ("Result: " ++ show res) $
                 track "\n" $
                 res

(//) :: Tm m -> Sbst m -> Tm m
t // (S0 :^^ _) = t
V // (ST (_ :<>: ((_ := t), _)) :^^ 0) = t
P ((tl, thl) :<>: (tr, thr)) // sg =
  P ((tl // sgl, phl) :<>: (tr // sgr, phr)) where
  (sgl, phl) = sbstSel thl sg
  (sgr, phr) = sbstSel thr sg
((x := b) :. t) // (sg :^^ w) = (x := b) :. (t // (sg :^^ if b then w+1 else w))
(m :$ rh) // sg = m :$ (rh /// sg)

(///) :: Sbst m -> Sbst m -> Sbst m
(S0 :^^ _) /// sg = sg
rh /// (S0 :^^ _) = rh
(rh :^^ v) /// (sg :^^ w) =
  case euclid w v of
    LtBy d -> case sg of
      ST ((sg, phl) :<>: t) ->
        (ST (((rh :^^ (d-1)) /// sg, phl) :<>: t) :^^ w)
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
      ST ((rh, thl) :<>: ((x := s), thr)) -> let
        (sgl, phl) = sbstSel thl (sg :^^ d)
        (sgr, phr) = sbstSel thr (sg :^^ d)
        in (ST ((rh /// sgl, phl) :<>: (x := (s // sgr), phr)) :^^ v)
      {-
        -------  ;  -------
           v           v
        -------     -------
        ----> s     -------
           rh          d
                    -------
                       sg
      -}
