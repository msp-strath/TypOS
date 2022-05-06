{-# LANGUAGE OverloadedStrings #-}
module Machine.Trace where

import Control.Monad.Reader
import Control.Monad.Writer

import Data.Bifunctor (first)
import Data.List (intersperse)
import qualified Data.Map as Map
import Data.Maybe (fromJust)

import ANSI hiding (withANSI)
import Actor (JudgementForm)
import Bwd
import Concrete.Base (Actor(..), Variable(..), Raw, Mode(..), ExtractMode(..))
import Concrete.Pretty()
import Doc hiding (render)
import Doc.Render.Terminal
import Format
import LaTeX
import Location (unknown)
import Machine.Base
import Options
import Pretty
import Syntax (SyntaxDesc, SyntaxTable, SyntaxCat, expand, VSyntaxDesc (..), contract)
import Term.Base
import Thin (DB(..))
import Unelaboration

data Trace e i
   = Node i [Trace e i]
   | Error e

instance (Show e, Show i) => Show (Trace e i) where
  show = unlines . go "" where

    go indt (Node i ts) = (indt ++ show i) : concatMap (go (' ':indt)) ts
    go indt (Error e)   = [indt ++ show e]

data Step jd db t
  = BindingStep Variable
  | NotedStep
  | PushingStep jd db (SyntaxDesc, t)
  | CallingStep jd [((Mode,SyntaxDesc), t)]
  deriving (Show)

type AStep = (ExtractMode, Step JudgementForm DB Term)
type CStep = Step Variable Variable Raw

instance Instantiable AStep where
  type Instantiated AStep = AStep
  instantiate st (em, step) = (em,) $ case step of
    BindingStep x -> BindingStep x
    NotedStep -> NotedStep
    PushingStep jd db t -> PushingStep jd db (instantiate st <$> t)
    CallingStep jd tr -> CallingStep jd ((instantiate st <$>) <$> tr)

data Error t
  = StuckUnifying t t
  | Failed String
  deriving (Show)

type AError = Error Term
type CError = Error Raw

instance Instantiable AError where
  type Instantiated AError = AError
  instantiate st = \case
    StuckUnifying s t -> StuckUnifying (instantiate st s) (instantiate st t)
    Failed s -> Failed s

instance (Instantiable e, Instantiable i) => Instantiable (Trace e i) where
  type Instantiated (Trace e i) = Trace (Instantiated e) (Instantiated i)
  instantiate st (Node i ts) = Node (instantiate st i) (instantiate st <$> ts)
  instantiate st (Error e)   = Error (instantiate st e)

instance Unelab AError where
  type Unelabed AError = CError
  type UnelabEnv AError = Naming
  unelab (StuckUnifying s t) = do
    s <- unelab s
    t <- unelab t
    pure $ StuckUnifying s t
  unelab (Failed s) = pure $ Failed s

instance Unelab (Trace AError AStep) where
  type Unelabed (Trace AError AStep) = Trace CError CStep
  type UnelabEnv (Trace AError AStep) = Naming
  unelab (Node (em, s) ts) = case s of
    BindingStep (Variable r x) -> do
      na <- ask
      let y = freshen x na
      ts <- local (`nameOn` y) $ traverse unelab ts
      pure (Node (BindingStep (Variable r y)) ts)
    NotedStep -> Node NotedStep <$> traverse unelab ts
    PushingStep jd db (d, t) -> do
      jd <- subunelab jd
      v <- unelab db
      t <- unelab t
      Node (PushingStep jd v (d, t)) <$> traverse unelab ts
    CallingStep jd tr -> do
      jd <- subunelab jd
      tr <- traverse (traverse unelab) tr
      Node (CallingStep jd tr) <$> traverse unelab ts
  unelab (Error e) = Error <$> unelab e

instance Pretty (Mode, Raw) where
  pretty (m, t) = withANSI [ SetColour Background (pick m) ] (pretty t) where

    pick :: Mode -> Colour
    pick Input = Blue
    pick Output = Red

instance Pretty CStep where
  pretty = \case
    BindingStep x -> withANSI [ SetColour Background Magenta ] ("\\" <> pretty x <> dot)
    PushingStep jd x (_, t) -> pretty jd <+> braces (hsep [pretty x, "->", pretty t]) <> dot
    CallingStep jd pts -> pretty jd <+> sep (pretty <$> map (first fst) pts)
    NotedStep -> ""

instance Pretty CError where
  pretty = \case
    StuckUnifying s t -> withANSI [ SetColour Background Yellow ]
                          (pretty s <+> "/~" <+> pretty t)
    Failed s -> withANSI [ SetColour Background Red ] (pretty s)

instance Pretty (Trace CError CStep) where
  pretty (Node i@(BindingStep x) ts) =
    let (prf, suf) = getPushes x ts in
    vcat ( hsep (pretty <$> i:prf) : map (indent 1 . pretty) suf)
  pretty (Node i ts) = vcat (pretty i : map (indent 1 . pretty) ts)
  pretty (Error e) = pretty e

instance LaTeX CStep where
  type Format CStep = ()
  toLaTeX _ = \case
    BindingStep x -> do
      x <- toLaTeX () x
      pure $ call False "typosBinding" [x]
    PushingStep jd x (d, t) -> do
      jd <- toLaTeX () jd
      x <- toLaTeX () x
      t <- toLaTeX d t
      pure $ call False "typosPushing" [jd, x, t]
    CallingStep jd pts -> do
      jd <- toLaTeX () jd
      pts <- traverse (uncurry toLaTeX . first snd) pts
      pure $ call False ("calling" <> jd) pts
    NotedStep -> pure ""

instance LaTeX CError where
  type Format CError = ()
  toLaTeX _ = \case
    StuckUnifying s t -> do
      let d = Syntax.contract VWildcard
      s <- toLaTeX d s
      t <- toLaTeX d t
      pure $ call False "typosStuckUnifying" [s, t]
    Failed s -> call False "typosFailed" . pure <$> toLaTeX () s

instance LaTeX (Trace CError CStep) where
  type Format (Trace CError CStep) = ()
  toLaTeX n (Node i []) = do
    i <- toLaTeX () i
    pure $ call False "typosAxiom" [i]
  toLaTeX n (Node i@(BindingStep x) ts) = do
    let (prf, suf) = getPushes x ts
    i <- toLaTeX () i
    prf <- traverse (toLaTeX ()) prf
    suf <- traverse (toLaTeX ()) suf
    pure $ typosDerivation (i <> hsep (intersperse "\\ " prf)) suf

  toLaTeX n (Node i ts) = do
    i <- toLaTeX () i
    ts <- traverse (toLaTeX ()) ts
    pure $ typosDerivation i ts

  toLaTeX n (Error e) = do
    e <- toLaTeX () e
    pure $ call False "typosError" [e]

typosDerivation :: Doc () -> [Doc ()] -> Doc ()
typosDerivation i ts =
   call True "typosDerivation"
     [ i
     , vcat (call False "typosBeginPrems" []
            : intersperse (call False "typosBetweenPrems" []) ts
            ++ [call False "typosEndPrems" []])]

getPushes :: Variable -> [Trace CError CStep] -> ([CStep], [Trace CError CStep])
getPushes x [Node i@(PushingStep _ y _) ts] | x == y =
      let (prf, suf) = getPushes x ts in
      (i:prf, suf)
getPushes _ ts = ([], ts)

extract :: [Frame] -> [Trace AError AStep]
extract [] = []
extract (f : fs) = case f of
  LeftBranch Hole p -> extract fs ++ extract (stack p) ++ findFailures p
  RightBranch p Hole -> extract (stack p) ++ extract fs ++ findFailures p
  Spawnee Interface{..} -> let p = snd spawner in
    Node (extractionMode, CallingStep judgeName (zip judgeProtocol (traffic <>> []))) (extract fs)
    : extract (stack p) ++ findFailures p
  Spawner Interface{..} -> let p = fst spawnee in
    Node (extractionMode, CallingStep judgeName (zip judgeProtocol (traffic <>> []))) (extract (stack p) ++ findFailures p)
    : extract fs
  Pushed jd (i, d, t) -> node (AlwaysExtract, PushingStep jd i (d, t))
  Binding x -> node (AlwaysExtract, BindingStep (Variable unknown x))
  UnificationProblem date s t -> Error (StuckUnifying s t) : extract fs
  Noted -> Node (AlwaysExtract, NotedStep) [] : extract fs
  _ -> extract fs

  where
    findFailures :: Process Status [] -> [Trace AError AStep]
    findFailures p@Process{..}
     = case actor of
         Fail _ [StringPart e] -> [Error (Failed e)]
         Fail _ _ -> error "Expected `Fail` message to be singleton string"
         _ -> []

    node :: AStep -> [Trace AError AStep]
    node s = [Node s (extract fs)]

cleanup :: [Trace AError AStep] -> [Trace AError AStep]
cleanup = snd . go False [] where

  go :: Bool            -- ^ is the parent suppressable?
     -> [JudgementForm] -- ^ list of toplevel judgements already seen
     -> [Trace AError AStep] -> (Any, [Trace AError AStep])
  go supp seen [] = pure []
  go supp seen (Node (em, i@(CallingStep jd tr)) ts : ats)
    | em == InterestingExtract || jd `elem` seen
    = let (Any b, ts') = go True seen ts in
      if not supp && b
        then (Node (em, i) ts' :) <$> go supp seen ats
        else (ts' ++) <$ tell (Any b) <*> go supp seen ats
    | em == TopLevelExtract
    = (:) <$> censor (const (Any False)) (Node (em, i) <$> go False (jd : seen) ts)
          <*> go supp seen ats
    | otherwise
    = (:) <$> censor (const (Any False)) (Node (em, i) <$> go False [] ts)
          <*> go supp seen ats
  go supp seen (Node (em, NotedStep) _ : ats) = tell (Any True) >> go supp seen ats
  go supp seen (Node i ts : ats) =
    (:) <$> censor (const (Any False)) (Node i <$> go False seen ts)
        <*> go supp seen ats
  go supp seen (Error e : ats) =
    (Error e :) <$> go supp seen ats

diagnostic :: Options -> StoreF i -> [Frame] -> String
diagnostic opts st fs =
  let ats = cleanup $ extract fs in
  let iats = instantiate st ats in
  let cts = traverse unelab iats in
  render (colours opts) ((initConfig (termWidth opts)) { orientation = Vertical })
    $ vcat $ map pretty $ unsafeEvalUnelab initNaming cts


mkNewCommand :: String -> Int -> String -> String
mkNewCommand cmd ar body
  = "\\newcommand{\\" <> cmd <> "}[" <> show ar <> "]{" <> body <> "}"

mkTag :: String -> String
mkTag e = "\\mathsf{" ++ e ++ "}"

nArgs :: Int -> [String]
nArgs n = map (("\\ #" ++) . show) [1..n]

syntaxPreamble :: SyntaxTable -> SyntaxCat -> [Doc ()]
syntaxPreamble table cat = go (fromJust $ Map.lookup cat table) where

  go :: SyntaxDesc -> [Doc ()]
  go t = case Syntax.expand Map.empty t of
    Just (VCons d e) -> go d ++ go e
    Just (VEnumOrTag es tds) ->
        map (\ e -> text $ mkNewCommand ("enum" ++ e) 0 (mkTag e)) es ++
        map (\ (t, ds) -> text $ mkNewCommand ("tag" ++ t) (length ds)
                               $ unwords ("[" : (mkTag t) : nArgs (length ds) ++ ["]"])) tds
    _ -> []

judgementPreamble :: Frame -> [Doc ()]
judgementPreamble (Rules jd jp _)
  = [text $ mkNewCommand ("calling" ++ jd) (length jp)
          $ "\\textsc{" ++ jd ++ "}" ++ unwords (nArgs (length jp))
    ]
judgementPreamble _ = []

ldiagnostic :: SyntaxTable -> StoreF i -> [Frame] -> String
ldiagnostic table st fs =
  let ats = cleanup $ extract fs in
  let iats = instantiate st ats in
  let cts = traverse unelab iats in
  let rts = unsafeEvalUnelab initNaming cts in
  let dts = (`evalLaTeXM` table) (traverse (toLaTeX ()) rts) in
  show $ vcat $
   [ "\\documentclass[multi=page]{standalone}"
   , ""
   , "%%%%%%%%%%% Packages %%%%%%%%%%%%%%%%%%%"
   , "\\usepackage{xcolor}"
   , "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
   , ""
   , "%%%%%%%%%%% Notations %%%%%%%%%%%%%%%%%%"
   , "\\newcommand{\\typosBinding}[1]{#1 \\vdash}"
   , "\\newcommand{\\typosPushing}[3]{\\textsc{#1} \\lbrace #2 \\to #3 \\rbrace.}"
   , "\\newcommand{\\typosStuckUnifying}[2]{#1 \\not\\sim #2}"
   , "\\newcommand{\\typosFailed}[1]{\\text{#1}}"
   , "\\newcommand{\\typosAtom}[1]{\\tt`#1}"
   , "\\newcommand{\\typosNil}{[]}"
   , "\\newcommand{\\typosListStart}[2]{[#1#2}"
   , "\\newcommand{\\typosListEnd}{]}"
   , "\\newcommand{\\typosListTail}[1]{\\textbar #1]}"
   , "\\newcommand{\\typosScope}[2]{\\lambda #1. #2}"
   , "\\newcommand{\\typosAxiom}[1]{#1}"
   , "\\newcommand{\\typosError}[1]{\\colorbox{red}{\\ensuremath{#1}}}"
   , "\\newcommand{\\typosDerivation}[2]{#1 \\\\ #2}"
   , "\\newcommand{\\typosBeginPrems}{\\begin{array}{|@{\\ }l@{}}}"
   , "\\newcommand{\\typosBetweenPrems}{\\\\}"
   , "\\newcommand{\\typosEndPrems}{\\end{array}}"
   , "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
   , ""
   ] ++
   concatMap (syntaxPreamble table) (Map.keys table)
   ++ concatMap judgementPreamble fs
   ++
   [ "%\\input{notations}"
   , ""
   , "%%%%%%%%%%% Derivations %%%%%%%%%%%%%%%%"
   , "\\begin{document}"
   ] ++
   (dts >>= \ der ->
      [ "\\begin{page}"
      , "$\\displaystyle"
      , "\\begin{array}{l}"
      , der
      , "\\end{array}"
      , "$"
      , "\\end{page}"
      , "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
      , ""
      ]) ++
   [ "\\end{document}"]
