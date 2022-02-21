{-# LANGUAGE DeriveFunctor #-}
module Pattern where

import qualified Data.Map as Map

import Control.Applicative

import Control.Monad.Reader

import Bwd
import Thin
import Hide
import Display
import Parse

import Term.Base

-- patterns are de Bruijn
data PatF v
  = VP v
  | AP String
  | PP (PatF v) (PatF v)
  | BP (Hide String) (PatF v)
  | MP String Th
  | GP
  deriving (Show, Functor, Eq)

type Pat = PatF Int

data PatVar = VarP Int
  deriving (Show, Eq)

instance Thable PatVar where
  VarP i *^ th = VarP (i *^ th)

bound :: Bwd String -> PatF v -> MetaScopes
bound xz (PP l r) = bound xz l <> bound xz r
bound xz (BP (Hide x) b) = bound (xz :< x) b
bound xz (MP m th) = Map.singleton m (th ^? xz)
bound _ _ = mempty

instance Thable v => Thable (PatF v) where
  VP v *^ th = VP (v *^ th)
  AP a *^ th = AP a
  PP p q *^ th = PP (p *^ th) (q *^ th)
  BP x b *^ th = BP x (b *^ (th -? True))
  MP m ph *^ th = MP m (ph *^ th)
  GP *^ th = GP

instance Selable (PatF PatVar) where
  th ^? VP (VarP v) = maybe GP (VP . VarP) (thickx th v)
  th ^? AP a = AP a
  th ^? PP p q = PP (th ^? p) (th ^? q)
  th ^? BP x b = BP x ((th -? True) ^? b)
  th ^? MP m ph = MP m (let (tph, _, _) = pullback th ph in tph)
  th ^? GP = GP

(#?) :: String -> [PatF v] -> PatF v
a #? ts = foldr PP (AP "") (AP a : ts)

-- match assumes that p's vars are the local end of t's
match :: Root
      -> Pat
      -> Term
      -> Maybe (Root, (Map.Map String Meta, Map.Map Meta Term))
match r (MP x ph) (CdB (t, th)) = do
  let g = bigEnd th - bigEnd ph  -- how many globals?
  ps <- thicken (ones g <> ph) th
  let (m, r') = meta r x
  return (r', (Map.singleton x m, Map.singleton m (CdB (t, ps))))
match r p t = case (p, expand t) of
  (VP i, VX j _) | i == j -> return (r, (Map.empty, Map.empty))
  (AP a, AX b _) | a == b -> return (r, (Map.empty, Map.empty))
  (PP p q, s :%: t) -> do
    (r, m) <- match r p s
    (r, n) <- match r q t
    return (r, m <> n)
  (BP _ p, _ :.: t) -> match r p t
  _ -> empty

-- Parsing

instance Lisp Pat where
  mkNil = const (AP "")
  mkCons = PP
  pCar = ppat

ppat :: Parser Pat
ppat = pvar (\ str -> MP str . ones <$> plen) (pure . VP)
  <|> AP <$> patom
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ppat <* pspc <* pch (== ')')
  <|> id <$ pch (== '\\') <* pspc <*> (do
    x <- pnom
    pspc
    pch (== '.')
    pspc
    BP (Hide x) <$> pbind x ppat)
  <|> id <$ pch (== '{') <*> do
    (th, xz) <- pth
    pspc
    (*^ th) <$> plocal xz ppat

pth :: Parser (Th, Bwd String)
pth = do
  (xns, b) <- raw
  xz <- pscope
  let xnz = deBruijnify xz
  let th = (if b then comp else id) (which (`elem` xns) xnz)
  pure (th, th ^? xz)

  where

  raw :: Parser ([(String, Int)], Bool)
  raw = (,) <$> many (id <$ pspc <*> pvar') <* pspc
            <*> (True <$ pch (== '*') <* pspc <|> pure False)
            <* pch (== '}')

-- Displaying

instance Display t => Display (PatF t) where
  display = \case
    VP n -> display n
    AP ""  -> pure "[]"
    AP str -> pure $ "'" ++ str
    PP p q -> do
      p <- pdisplay p
      q <- displayPatCdr q
      pure $ "[" ++ p ++ q ++ "]"
    BP (Hide x) p -> do
      p <- local (`nameOn` x) $ display p
      pure $ "\\" ++ x ++ "." ++ p
    MP m th -> pure m

  pdisplay p = case p of
    AP{} -> display p
    PP{} -> display p
    _ -> pdisplayDFT p

displayPatCdr :: Display t => PatF t -> DisplayM String
displayPatCdr (AP "") = pure ""
displayPatCdr (PP p q) = do
  p <- pdisplay p
  q <- displayPatCdr q
  pure $ " " ++ p ++ q
displayPatCdr t = do
  t <- display t
  pure $ "|" ++ t
