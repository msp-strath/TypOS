{-# LANGUAGE TypeSynonymInstances #-}

module Term.Display where

import Data.List

import Control.Monad.Except
import Control.Monad.Reader

import Bwd
import Thin
import Hide
import Term

import Display

instance Display m => Display (Tm m) where
  display = \case
    V -> asks naming >>= \case
           (B0 :< x, _, _) -> pure x
           na                -> throwError (VarOutOfScope na)
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
              na <- asks naming
              let y = freshen x na
              t <- local (`nameOn` y) $ display t
              pure ("\\" ++ y ++ "." ++ t)
    m :$ sg -> do
      -- the current naming is not for the right scope after subsituting, so we require m to be closed for now
      m  <- local (setNaming initNaming) $ display m
      sg <- display sg
      pure (sg ++ m)

  pdisplay t = case t of
    A{} -> display t
    P{} -> display t
    _ -> pdisplayDFT t

instance Display Meta where
  display (Meta ns) = pure $ show ns -- TODO: do better

instance Display m => Display (CdB (Tm m)) where
  display  (CdB (t', th)) = local (nameSel th) $ display t'
  pdisplay (CdB (t', th)) = local (nameSel th) $ pdisplay t'

displayCdr :: Display m => Tm m -> DisplayM String
displayCdr (A "") = pure ""
displayCdr (P (s :<>: t)) = do
  s <- pdisplay s
  t <- displayCdr' t
  pure (" " ++ s ++ t)
displayCdr t = do
  t <- display t
  pure ("|" ++ t)

displayCdr' :: Display m => CdB (Tm m) -> DisplayM  String
displayCdr' (CdB (t', th)) = local (nameSel th) $ displayCdr t'

instance Display m => Display (Sbst m) where
  display sg = displaySg sg >>= \case
    [] -> pure []
    sg' -> pure $ "{" ++ intercalate "," sg' ++ "}"

   where

     displaySg :: Display m => Sbst m -> DisplayM [String]
     displaySg sg = do
       na@(_, th, _) <- asks naming
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
              sg <- local (setNaming (xz, th, yz)) $ displaySg (sg :^^ w)
              pure ((y ++ "*") : sg)
            (th, True) ->
              case xz of
                xz :< x -> do
                  sg <- local (setNaming (xz, th, yz)) $ displaySg (sg :^^ (w - 1))
                  pure (x : sg)
                _ -> throwError $ InvalidNaming na
           _ -> throwError $ InvalidNaming na
