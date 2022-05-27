{-# LANGUAGE DeriveFunctor #-}
module Pattern where

import qualified Data.Map as Map

import Control.Applicative

import Thin
import Hide

import Term.Base

-- patterns are de Bruijn
data Pat
  = AT String Pat
  | VP DB
  | AP String
  | PP Pat Pat
  | BP (Hide String) Pat
  | MP String Th
  | GP -- grumpy pattern
  | HP -- happy pattern
  deriving (Show, Eq)

instance Thable Pat where
  AT v p *^ th = AT v (p *^ th)
  VP v *^ th = VP (v *^ th)
  AP a *^ th = AP a
  PP p q *^ th = PP (p *^ th) (q *^ th)
  BP x b *^ th = BP x (b *^ (th -? True))
  MP m ph *^ th = MP m (ph *^ th)
  GP *^ th = GP
  HP *^ th = HP

instance Selable Pat where
  th ^? AT v p = AT v (th ^? p)
  th ^? VP v = maybe GP VP (thickx th v)
  th ^? AP a = AP a
  th ^? PP p q = PP (th ^? p) (th ^? q)
  th ^? BP x b = BP x ((th -? True) ^? b)
  th ^? MP m ph = MP m (let (tph, _, _) = pullback th ph in tph)
  th ^? GP = GP
  th ^? HP = HP

(#?) :: String -> [Pat] -> Pat
a #? ts = foldr PP (AP "") (AP a : ts)

-- match assumes that p's vars are the local end of t's
match :: Root
      -> Pat
      -> Term
      -> Maybe (Root, (Map.Map String Meta, Map.Map Meta Term))
match r (AT x p) t = do
  let (m, r') = meta r x
  (r, (ms, mts)) <- match r' p t
  pure (r, (Map.insert x m ms, Map.insert m t mts))
match r (MP x ph) (CdB t th) = do
  let g = bigEnd th - bigEnd ph  -- how many globals?
  ps <- thicken (ones g <> ph) th
  let (m, r') = meta r x
  return (r', (Map.singleton x m, Map.singleton m (CdB t ps)))
match r p t = case (p, expand t) of
  (VP i, VX j _) | i == j -> return (r, (Map.empty, Map.empty))
  (AP a, AX b _) | a == b -> return (r, (Map.empty, Map.empty))
  (HP, _) -> return (r, (Map.empty, Map.empty))
  (PP p q, s :%: t) -> do
    (r, m) <- match r p s
    (r, n) <- match r q t
    return (r, m <> n)
  (BP _ p, _ :.: t) -> match r p t
  _ -> empty
