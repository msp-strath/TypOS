{-# LANGUAGE OverloadedStrings #-}
module Machine.Trace where

import Control.Monad.Reader

import ANSI hiding (withANSI)
import Actor (JudgementForm)
import Concrete.Pretty()
import Machine.Base
import Pretty
import Term.Base
import Thin (DB(..))
import Bwd ((<>>))
import Unelaboration
import Concrete.Base (Variable(..), Raw, Mode(..))
import Doc hiding (render)
import Doc.Render.Terminal

data Trace i = Node i [Trace i]

instance Show i => Show (Trace i) where
  show = unlines . go "" where

    go indt (Node i ts) = (indt ++ show i) : concatMap (go (' ':indt)) ts

data Step jd db t
  = BindingStep String
  | PushingStep jd db t
  | CallingStep jd [(Mode,t)]
  deriving (Show)

type AStep = Step JudgementForm DB Term
type CStep = Step Variable Variable Raw

instance Instantiable AStep where
  type Instantiated AStep = AStep
  instantiate st = \case
    BindingStep x -> BindingStep x
    PushingStep jd db t -> PushingStep jd db (instantiate st t)
    CallingStep jd tr -> CallingStep jd ((instantiate st <$>) <$> tr)

instance Instantiable i => Instantiable (Trace i) where
  type Instantiated (Trace i) = Trace (Instantiated i)
  instantiate st (Node i ts) = Node (instantiate st i) (instantiate st <$> ts)

instance Unelab (Trace AStep) where
  type Unelabed (Trace AStep) = Trace CStep
  type UnelabEnv (Trace AStep) = Naming
  unelab (Node s ts) = case s of
    BindingStep x -> do
      na <- ask
      let y = freshen x na
      ts <- local (`nameOn` y) $ traverse unelab ts
      pure (Node (BindingStep y) ts)
    PushingStep jd db t -> do
      jd <- subunelab jd
      v <- unelab db
      t <- unelab t
      Node (PushingStep jd v t) <$> traverse unelab ts
    CallingStep jd tr -> do
      jd <- subunelab jd
      tr <- traverse (traverse unelab) tr
      Node (CallingStep jd tr) <$> traverse unelab ts

instance Pretty (Mode, Raw) where
  pretty (m, t) = withANSI [ SetColour Background (pick m) ] (pretty t) where

    pick :: Mode -> Colour
    pick Input = Blue
    pick Output = Red

instance Pretty CStep where
  pretty = \case
    BindingStep x -> withANSI [ SetColour Background Magenta ] ("\\" <> pretty x <> dot)
    PushingStep jd x t -> pretty jd <+> braces (hsep [pretty x, "->", pretty t])
    CallingStep jd ts -> pretty jd <+> sep (pretty <$> ts)

instance Pretty (Trace CStep) where
  pretty (Node i@(BindingStep x) ts) =
    let (prf, suf) = getPushes ts in
    vcat ( hsep (pretty <$> i:prf) : map (indent 1 . pretty) suf)

    where
    getPushes [Node i@(PushingStep _ y _) ts] | Variable x == y =
      let (prf, suf) = getPushes ts in
      (i:prf, suf)
    getPushes ts = ([], ts)

  pretty (Node i ts) = vcat (pretty i : map (indent 1 . pretty) ts)


extract :: [Frame] -> [Trace AStep]
extract [] = []
extract (f : fs) = case f of
  LeftBranch Hole p -> extract fs ++ extract (stack p)
  RightBranch p Hole -> extract (stack p) ++ extract fs
  Spawnee Interface{..} ->
    Node (CallingStep judgeName (zip (fst <$> judgeProtocol) (traffic <>> []))) (extract fs)
    : extract (stack (snd spawner))
  Spawner Interface{..} ->
    Node (CallingStep judgeName (zip (fst <$> judgeProtocol) (traffic <>> []))) (extract (stack (fst spawnee)))
    : extract fs
  Pushed jd (i, t) -> node (PushingStep jd i t)
  Binding x -> node (BindingStep x)
  _ -> extract fs

  where
    node :: AStep -> [Trace AStep]
    node s = [Node s (extract fs)]

data Tracing = Tracing
  { topLevel :: [JudgementForm]
  , never    :: [JudgementForm]
  }


cleanup :: Tracing -> [Trace AStep] -> [Trace AStep]
cleanup trac = go [] where

  go :: [JudgementForm] -> [Trace AStep] -> [Trace AStep]
  go seen [] = []
  go seen (Node i@(CallingStep jd tr) ts : ats)
    | jd `elem` never trac || jd `elem` seen
    = go seen ts ++ go seen ats
    | jd `elem` topLevel trac
    = Node i (go (jd : seen) ts) : go seen ats
    | otherwise = Node i (go [] ts) : go seen ats
  go seen (Node i ts : ats) = Node i (go seen ts) : go seen ats

diagnostic :: Tracing -> StoreF i -> [Frame] -> String
diagnostic trac st fs =
  let ats = cleanup trac $ extract fs in
  let iats = instantiate st ats in
  let cts = traverse unelab iats in
  render ((initConfig 0) { orientation = Vertical })
    $ vcat $ map pretty $ unsafeEvalUnelab initNaming cts
