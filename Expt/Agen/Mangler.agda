module Mangler where

open import Basics
open import Thin
open import Cop
open import Pair
open import Bind
open import Term

open THIN {`1}
open COP  {`1}
open PAIR {`1}
open BIND {`1}

module MANGLE (M M' : Nat -> Set)(A : Set) where

  module T  = TERM M A
  module T' = TERM M' A

  -- xi: global scope
  -- ga: local scope
  record Mangler (f : Set -> Set) (xi ga : Nat)
    : Set where
    coinductive
    field
--      mangTh : Maybe (ga <= xi)
      mangV  : forall {x} -> Only x ga
                 -> f (T'.Term (xi <<< ga))
      mangB  : forall {x} -> Mangler f xi (ga -, x)
      mangM  : forall {de} -> M de -> f ((xi <<< de) T'.%>^ (xi <<< ga))
                                     -> f (T'.Term (xi <<< ga))
      mangSelFrom : forall {ga0} -> ga0 <= ga -> Mangler f xi ga0

  open Mangler

  module _ {f : Set -> Set}{{App : Applicative f}} where

    open T

    mangle : forall {ga xi} -> Mangler f xi ga ->
             T.Tm ga -> f (T'.Term (xi <<< ga))
    mangleCdB : forall {ga0 xi ga} -> Mangler f xi ga ->
                T.Tm ga0 -> ga0 <= ga -> f (T'.Term (xi <<< ga))
    mangleS : forall xi {up ga} -> Mangler f xi ga ->
              up T.%> ga -> f ((xi <<< up) T'.%>^ (xi <<< ga))
    mangleCdBS : forall xi {ga0 up ga} -> Mangler f xi ga ->
                 up T.%> ga0 -> ga0 <= ga ->
                 f ((xi <<< up) T'.%>^ (xi <<< ga))

    mangle mu (vv x) = mangV mu x
    mangle mu (aa a) with a , _ <- mota a = pure (T'.a^ a)
    mangle mu (pp (a </ u \> b))
      = (| mangleCdB mu a (luth u) T'.,^ mangleCdB mu b (ruth u) |)
    mangle mu (bb (kk tm)) = ((kk - T'.bb) $^_) <$> mangle mu tm
    mangle mu (bb (ll tm)) = (| T'.b^ (mangle (mangB mu) tm) |)
    mangle mu (mm (m & sg)) = mangM mu m (mangleS _ mu sg)

    mangleCdB mu tm th = (_|^ (io +^+ th)) <$> mangle (mangSelFrom mu th) tm

    mangleS xi mu [] = pure (T'.is & io)
    mangleS xi mu (sg -, x) = adjust <$> mangleS xi (mangSelFrom mu (io -^ x)) sg where
      adjust : forall {ga de x} -> ga T'.%>^ de -> (ga -, x) T'.%>^ (de -, x)
      adjust (sg & th) = sg T'.-, x & th -, x
    mangleS xi mu ((sg </ u \> tm) -/ x)
      = (| (| mangleCdBS xi mu sg (luth u) /,\ mangleCdB mu tm (ruth u)|) T'.-/^ pure x |)

    mangleCdBS xi mu sg th = (_|^ (io +^+ th)) <$> mangleS xi (mangSelFrom mu th) sg
