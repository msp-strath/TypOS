{-# LANGUAGE FlexibleContexts #-}

module Term.Display where

import Data.List

import Control.Monad.Except
import Control.Monad.Reader

import Bwd
import Forget()
import Hide
import Term
import Thin

import Display

initNaming :: Naming
initNaming = (B0, ones 0, B0)

nameOn :: Naming -> String -> Naming
nameOn (xz, th, yz) x = (xz :< x, th -? True, yz :< x)

nameSel :: Th -> Naming -> Naming
nameSel th (xz, ph, yz) = (th ?< xz, th <^> ph, yz)

freshen :: String -> Naming -> String
freshen x (xz, _, _) = head [y | y <- ys, all (y /=) xz] where
  ys = x : [x ++ show (i :: Integer) | i <- [0..]]

instance Display0 m => Display (Tm m) where
  type DisplayEnv (Tm m) = Naming
  display = \case
    V -> ask >>= \case
           (B0 :< x, _, _) -> pure x
           na              -> throwError (VarOutOfScope na)
    A a -> case a of
             "" -> pure "[]"
             _  -> pure $ '\'' : a
    P (s :<>: t) -> do
      s <- pdisplay s
      t <- displayCdr' t
      pure ("[" ++ s ++ t ++ "]")
    (Hide x := b) :. t -> case b of
            False -> do
              t <- display t
              pure ("\\_." ++ t)
            True -> do
              na <- ask
              let y = freshen x na
              t <- local (`nameOn` y) $ display t
              pure ("\\" ++ y ++ "." ++ t)
    m :$ sg -> do
      -- the current naming is not for the right scope after subsituting, so we require m to be closed for now
      m  <- subdisplay m
      sg <- display sg
      pure (sg ++ m)

  pdisplay t = case t of
    A{} -> display t
    P{} -> display t
    _ -> pdisplayDFT t

instance Display Meta where
  type DisplayEnv Meta = ()
  display (Meta ns) = pure $ show ns -- TODO: do better

instance Display0 m => Display (CdB (Tm m)) where
  type DisplayEnv (CdB (Tm m)) = Naming
  display  (CdB (t', th)) = local (nameSel th) $ display t'
  pdisplay (CdB (t', th)) = local (nameSel th) $ pdisplay t'

displayCdr :: Display0 m => Tm m -> DisplayM Naming String
displayCdr (A "") = pure ""
displayCdr (P (s :<>: t)) = do
  s <- pdisplay s
  t <- displayCdr' t
  pure (" " ++ s ++ t)
displayCdr t = do
  t <- display t
  pure ("|" ++ t)

displayCdr' :: Display0 m => CdB (Tm m) -> DisplayM Naming String
displayCdr' (CdB (t', th)) = local (nameSel th) $ displayCdr t'

instance Display0 m => Display (Sbst m) where
  type DisplayEnv (Sbst m) = Naming
  display sg = displaySg sg >>= \case
    [] -> pure []
    sg' -> pure $ "{" ++ intercalate "," sg' ++ "}"

   where

     displaySg :: Display0 m => Sbst m -> DisplayM Naming [String]
     displaySg sg = do
       na@(_, th, _) <- ask
       case sg of
         (S0 :^^ _) | th == ones (bigEnd th) -> pure []
         (ST (CdB (sg, th) :<>: CdB ((Hide x := t), ph)) :^^ 0) -> do
           t <- display (CdB (t, ph))
           sg <- local (nameSel th) $ displaySg sg
           pure ((x ++ "=" ++ t) : sg)
         (sg :^^ w) -> case na of
           (_, th, _) | bigEnd th <= 0 -> throwError (UnexpectedEmptyThinning na)
           (xz, th, yz :< y) -> case thun th of
            (th, False) -> do
              sg <- local (const (xz, th, yz)) $ displaySg (sg :^^ w)
              pure ((y ++ "*") : sg)
            (th, True) ->
              case xz of
                xz :< x -> do
                  sg <- local (const (xz, th, yz)) $ displaySg (sg :^^ (w - 1))
                  pure (x : sg)
                _ -> throwError $ InvalidNaming na
           _ -> throwError $ InvalidNaming na
