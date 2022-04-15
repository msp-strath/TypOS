{-# LANGUAGE OverloadedStrings #-}
module Machine.Trace where

import Control.Monad.Reader
import Control.Monad.Writer

import Data.Bifunctor (first)
import Data.Maybe (fromJust)

import ANSI hiding (withANSI)
import Actor (JudgementForm)
import Concrete.Pretty()
import Machine.Base
import Pretty
import Term.Base
import Thin (DB(..))
import Bwd ((<>>))
import Unelaboration
import Concrete.Base (Variable(..), Raw, Mode(..), ExtractMode(..))
import Doc hiding (render)
import Doc.Render.Terminal
import Syntax (SyntaxDesc, SyntaxTable, SyntaxCat, expand, VSyntaxDesc (..))
import LaTeX
import qualified Data.Map as Map
import Data.List (intersperse)

data Trace i = Node i [Trace i]

instance Show i => Show (Trace i) where
  show = unlines . go "" where

    go indt (Node i ts) = (indt ++ show i) : concatMap (go (' ':indt)) ts

data Step jd db t
  = BindingStep String
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

instance Instantiable i => Instantiable (Trace i) where
  type Instantiated (Trace i) = Trace (Instantiated i)
  instantiate st (Node i ts) = Node (instantiate st i) (instantiate st <$> ts)

instance Unelab (Trace AStep) where
  type Unelabed (Trace AStep) = Trace CStep
  type UnelabEnv (Trace AStep) = Naming
  unelab (Node (em, s) ts) = case s of
    BindingStep x -> do
      na <- ask
      let y = freshen x na
      ts <- local (`nameOn` y) $ traverse unelab ts
      pure (Node (BindingStep y) ts)
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

instance Pretty (Mode, Raw) where
  pretty (m, t) = withANSI [ SetColour Background (pick m) ] (pretty t) where

    pick :: Mode -> Colour
    pick Input = Blue
    pick Output = Red

instance Pretty CStep where
  pretty = \case
    BindingStep x -> withANSI [ SetColour Background Magenta ] ("\\" <> pretty x <> dot)
    PushingStep jd x (_, t) -> pretty jd <+> braces (hsep [pretty x, "->", pretty t])
    CallingStep jd pts -> pretty jd <+> sep (pretty <$> map (first fst) pts)
    NotedStep -> ""

instance LaTeX CStep where
  type Format CStep = ()
  toLaTeX _ = \case
    BindingStep x -> pure $ call False "typosBinding" [text x]
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

instance LaTeX (Trace CStep) where
  type Format (Trace CStep) = ()
  toLaTeX n (Node i []) = do
    i <- toLaTeX () i
    pure $ call False "typosAxiom" [i]
  toLaTeX n (Node i@(BindingStep x) ts) = do
    let (prf, suf) = getPushes (Variable x) ts
    i <- toLaTeX () i
    prf <- traverse (toLaTeX ()) prf
    suf <- traverse (toLaTeX ()) suf
    pure $ typosDerivation (i <> hsep (intersperse "\\ " prf)) suf

  toLaTeX n (Node i ts) = do
    i <- toLaTeX () i
    ts <- traverse (toLaTeX ()) ts
    pure $ typosDerivation i ts

typosDerivation :: Doc () -> [Doc ()] -> Doc ()
typosDerivation i ts =
   call True "typosDerivation"
     [ i
     , vcat (call False "typosBeginPrems" []
            : intersperse (call False "typosBetweenPrems" []) ts
            ++ [call False "typosEndPrems" []])]

getPushes :: Variable -> [Trace CStep] -> ([CStep], [Trace CStep])
getPushes x [Node i@(PushingStep _ y _) ts] | x == y =
      let (prf, suf) = getPushes x ts in
      (i:prf, suf)
getPushes _ ts = ([], ts)


instance Pretty (Trace CStep) where
  pretty (Node i@(BindingStep x) ts) =
    let (prf, suf) = getPushes (Variable x) ts in
    vcat ( hsep (pretty <$> i:prf) : map (indent 1 . pretty) suf)
  pretty (Node i ts) = vcat (pretty i : map (indent 1 . pretty) ts)


extract :: [Frame] -> [Trace AStep]
extract [] = []
extract (f : fs) = case f of
  LeftBranch Hole p -> extract fs ++ extract (stack p)
  RightBranch p Hole -> extract (stack p) ++ extract fs
  Spawnee Interface{..} ->
    Node (extractionMode, CallingStep judgeName (zip judgeProtocol (traffic <>> []))) (extract fs)
    : extract (stack (snd spawner))
  Spawner Interface{..} ->
    Node (extractionMode, CallingStep judgeName (zip judgeProtocol (traffic <>> []))) (extract (stack (fst spawnee)))
    : extract fs
  Pushed jd (i, d, t) -> node (AlwaysExtract, PushingStep jd i (d, t))
  Binding x -> node (AlwaysExtract, BindingStep x)
  Noted -> Node (AlwaysExtract, NotedStep) [] : extract fs
  _ -> extract fs

  where
    node :: AStep -> [Trace AStep]
    node s = [Node s (extract fs)]

cleanup :: [Trace AStep] -> [Trace AStep]
cleanup = snd . go False [] where

  go :: Bool            -- ^ is the parent suppressable?
     -> [JudgementForm] -- ^ list of toplevel judgements already seen
     -> [Trace AStep] -> (Any, [Trace AStep])
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

diagnostic :: StoreF i -> [Frame] -> String
diagnostic st fs =
  let ats = cleanup $ extract fs in
  let iats = instantiate st ats in
  let cts = traverse unelab iats in
  render ((initConfig 80) { orientation = Vertical })
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
   [ "\\documentclass{article}"
   , "\\newcommand{\\typosBinding}[1]{#1 \\vdash}"
   , "\\newcommand{\\typosPushing}[3]{\\textsc{#1} \\lbrace #2 \\to #3 \\rbrace.}"
   , "\\newcommand{\\typosAtom}[1]{'#1}"
   , "\\newcommand{\\typosNil}{[]}"
   , "\\newcommand{\\typosListStart}[2]{[#1#2}"
   , "\\newcommand{\\typosListEnd}{]}"
   , "\\newcommand{\\typosListTail}[1]{\\textbar #1]}"
   , "\\newcommand{\\typosScope}[2]{\\backslash #1. #2}"
   , "\\newcommand{\\typosAxiom}[1]{#1}"
   , "\\newcommand{\\typosDerivation}[2]{#1 \\\\ #2}"
   , "\\newcommand{\\typosBeginPrems}{\\begin{array}{|@{\\ }l@{}}}"
   , "\\newcommand{\\typosBetweenPrems}{\\\\}"
   , "\\newcommand{\\typosEndPrems}{\\end{array}}"
   ] ++
   concatMap (syntaxPreamble table) (Map.keys table)
   ++ concatMap judgementPreamble fs
   ++
   [ "\\include{notations}"
   , "\\begin{document}"
   ] ++
   (dts >>= \ der ->
      [ "\\["
      , "\\begin{array}{l}"
      , der
      , "\\end{array}"
      , "\\]"
      ])
   ++ [ "\\end{document}"]
