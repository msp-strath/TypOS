{-# LANGUAGE UndecidableInstances, OverloadedStrings #-}

module Machine.Display where

import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Map as Map

import ANSI hiding (withANSI)
import Actor
import Actor.Display ()
import Concrete.Base
import Display
import Doc
import Doc.Render.Terminal
import Elaboration.Pretty()
import Forget
import Format
import Machine.Base
import Options
import Pretty
import Term
import Term.Display ()
import Unelaboration (DAEnv, initDAEnv, Naming, nameOn, initNaming)
import qualified Unelaboration as A

instance Display Date where
  type DisplayEnv Date = ()
  display (Date i) = pure $ pretty (show i)

instance Display Status where
  type DisplayEnv Status = ()
  display = \case
    StuckOn d -> display d
    New -> pure "New"
--    Done -> pure "Done"

instance Display Hole where
  type DisplayEnv Hole = ()
  display Hole = pure "<>"

data DEnv = DEnv
  { objectNaming :: Naming
  , daEnv :: DAEnv
  }

initDEnv :: DEnv
initDEnv = DEnv initNaming initDAEnv

instance Forget DEnv DAEnv where
  forget = daEnv

instance Forget DEnv Naming where
  forget = objectNaming

instance Forget DEnv DEnv where
  forget = id

initChildDEnv :: Channel -> DEnv -> DEnv
initChildDEnv ch de = de { daEnv = A.declareChannel ch $ initDAEnv }

declareChannel :: Channel -> DEnv -> DEnv
declareChannel ch de@DEnv{..} = de { daEnv = A.declareChannel ch daEnv }

instance ( Display c, Forget DEnv (DisplayEnv c)
         , Display p, Forget DEnv (DisplayEnv p)) => Display (Interface c p) where
  type DisplayEnv (Interface c p) = DEnv
  display (Interface (c, cch) ((pch, xs), p) jd _ _ tr) = do
    c <- local (initChildDEnv cch) $ subdisplay c
    cch' <- subdisplay cch
    pch' <- subdisplay pch
    p <- local (declareChannel pch) $ subdisplay p
    pure $ usingConfig $ \ cfg -> case orientation cfg of
      Vertical -> vcat $ brackets (cch' <> pipe <> pch' <> horizontally (collapse (pretty <$> xs)))
                       : map (indent 1) [ c, p ]
      Horizontal -> hsep [ c, "@", cch', pipe, pch', collapse (pretty <$> xs), "@", p ]

instance Display Frame where
  type DisplayEnv Frame = DEnv
  display = \case
    Rules jd _ (ch, a) -> do
      ch' <- subdisplay ch
      a <- local (declareChannel ch) $ subpdisplay a
      pure $ pretty jd <+> "|-@" <> ch' <> " {}" -- a
    LeftBranch Hole p -> do
      p <- display p
      pure $ "<> |" <+> p
    RightBranch p Hole -> do
      p <- display p
      pure $ p <+> "| <>"
    Spawnee intf -> display intf
    Spawner intf -> display intf -- pure $ withANSI [ SetColour Background Yellow ] $ show intf -- display intf
    Sent ch (xs, t) -> do
      ch' <- subdisplay ch
      t <- subpdisplay t -- pure $ show t
      pure $ withANSI [SetColour Foreground Blue, SetWeight Bold]
           $ "!" <> ch' <> dot <+> horizontally (collapse (pretty <$> xs)) <+> t
    Pushed jd (p, t) -> do
      p <- subdisplay p
      t <- subdisplay t
      pure $ hsep [pretty jd, "{", p, "->", t, "}. "]
    Binding x ->
      pure $ withANSI [SetColour Foreground Yellow, SetWeight Bold]
           $ backslash <> pretty x <> ". "
    UnificationProblem date s t -> do
      s <- subdisplay s
      t <- subdisplay t
      date <- subdisplay date
      pure $ withANSI [SetColour Background Red]
           $ s <+> "~?" <> brackets date <+> t
    Noted -> pure "Noted"

instance (Show (t Frame), Traversable t, Collapse t, Display0 s) => Display (Process s t) where
  type DisplayEnv (Process s t) = DEnv
  display p =  do
    (fs', store', env', a') <- displayProcess' p
    pure $ parens $ usingConfig $ \ cfg ->
      let osep = case orientation cfg of { Vertical -> sep; Horizontal -> hsep } in
      osep ([collapse fs', store', env'] ++ case actor p of {Win -> []; _ -> [a']})

displayProcess' :: (Traversable t, Collapse t, Display0 s) =>
  Process s t -> DisplayM DEnv (t (Doc Annotations), Doc Annotations, Doc Annotations, Doc Annotations)
displayProcess' Process{..} = do
  de <- ask
  (fs', de) <- runStateT (traverse go stack) de
  local (const de) $ do
    store' <- subdisplay store
    env' <- subpdisplay env
    a' <- subpdisplay actor
    pure (fs', store', case actor of Win -> ""; _ -> env', a')

    where

    go :: Frame -> StateT DEnv (DisplayM DEnv) (Doc Annotations)
    go f = do
      de <- get
      dis <- local (const de) $ lift $ display f
      put (de `frameOn` f)
      pure dis

type Store = StoreF Naming

instance Display Store where
  type DisplayEnv Store = ()
  display st = do
    tst <- display (today st)
    sols <- traverse go $ Map.toList $ solutions st
    pure $ tst <> colon <+>
                 withANSI [SetColour Background Green
                          , SetColour Foreground Black]
                 (collapse sols)
    where
    go :: (Meta, (Naming, Term)) -> DisplayM () (Doc Annotations)
    go (k, (na, t)) = do
      t <- withEnv na $ display t
      k <- subdisplay k
      pure $ k <+> ":=" <+> t


instance Display MachineStep where
  type DisplayEnv MachineStep = ()
  display = pure . pretty

frameOn :: DEnv -> Frame -> DEnv
frameOn de@DEnv{..} = \case
  Binding x -> de { objectNaming = objectNaming `nameOn` x
                  , daEnv = A.updateNaming (`nameOn` x) daEnv
                  }
  Spawnee (Interface (Hole, ch) _ _ _ _ _) -> initChildDEnv ch de
  Spawner (Interface _ ((ch, _), Hole) _ _ _ _) -> declareChannel ch de
  _ -> de

frDisplayEnv :: Foldable t => t Frame -> DEnv
frDisplayEnv = foldl frameOn initDEnv

insertDebug :: (Traversable t, Collapse t, Display0 s)
            => Process s t -> [Format dir Debug a] -> [Format dir (Doc Annotations) a]
insertDebug p fmt = map go fmt where

  (fs, st, en, _) = unsafeEvalDisplay initDEnv (displayProcess' p)
  go = \case
    TermPart d t -> TermPart d t
    StringPart str -> StringPart str
    DebugPart dbg -> DebugPart $ case dbg of
      ShowEnv -> en
      ShowStack -> collapse fs
      ShowStore -> st
