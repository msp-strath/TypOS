{-# LANGUAGE OverloadedStrings, UndecidableInstances, ScopedTypeVariables #-}
module Machine.Trace where

import Control.Monad.Reader
import Control.Monad.Writer

import Data.List (intersperse)
import qualified Data.Map as Map
import Data.Maybe (fromJust)

import ANSI hiding (withANSI)
import Actor (JudgementForm)
import Bwd
import Concrete.Base
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
import Unelaboration

data Trace ann e i
   = Node ann i [Trace ann e i]
   | Error ann e

instance (Show e, Show i) => Show (Trace ann e i) where
  show = unlines . go "" where

    go indt (Node _ i ts) = (indt ++ show i) : concatMap (go (' ':indt)) ts
    go indt (Error _ e)   = [indt ++ show e]

type family ITERM (ph :: Phase) :: *
type instance ITERM Abstract = Term
type instance ITERM Concrete = Raw

data ARGUMENT (ph :: Phase) ann = Argument
  { argMode :: Mode
  , argDesc :: SyntaxDesc
  , argTerm :: ITERM ph
  , argAnn  :: ann
  } deriving (Functor)

type AArgument ann = ARGUMENT Abstract ann
type CArgument ann = ARGUMENT Concrete ann

deriving instance
  ( Show (ITERM ph)
  , Show ann) =>
  Show (ARGUMENT ph ann)

data STEP (ph :: Phase) ann
  = BindingStep Variable
  | NotedStep
  | PushingStep (STACK ph) (TERMVAR ph) (SyntaxDesc, ITERM ph)
  | CallingStep (JUDGEMENTFORM ph) [ARGUMENT ph ann]
  deriving (Functor)

deriving instance
  ( Show (JUDGEMENTFORM ph)
  , Show (CHANNEL ph)
  , Show (BINDER ph)
  , Show (ACTORVAR ph)
  , Show (SYNTAXDESC ph)
  , Show (TERMVAR ph)
  , Show (ITERM ph)
  , Show (PATTERN ph)
  , Show (CONNECT ph)
  , Show (STACK ph)
  , Show (STACKDESC ph)
  , Show ann) =>
  Show (STEP ph ann)

type AStep ann = (ExtractMode, STEP Abstract ann)
type CStep ann = STEP Concrete ann

instance Instantiable (AArgument ann) where
  type Instantiated (AArgument ann) = AArgument ann
  instantiate st (Argument mode desc term ann)
    = Argument mode desc (instantiate st term) ann

instance Instantiable (AStep ann) where
  type Instantiated (AStep ann) = AStep ann
  instantiate st (em, step) = (em,) $ case step of
    BindingStep x -> BindingStep x
    NotedStep -> NotedStep
    PushingStep jd db t -> PushingStep jd db (instantiate st <$> t)
    CallingStep jd tr -> CallingStep jd (instantiate st <$> tr)

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

instance (Instantiable e, Instantiable i) => Instantiable (Trace ann e i) where
  type Instantiated (Trace ann e i) = Trace ann (Instantiated e) (Instantiated i)
  instantiate st (Node a i ts) = Node a (instantiate st i) (instantiate st <$> ts)
  instantiate st (Error a e)   = Error a (instantiate st e)

instance Unelab AError where
  type Unelabed AError = CError
  type UnelabEnv AError = Naming
  unelab (StuckUnifying s t) = do
    s <- unelab s
    t <- unelab t
    pure $ StuckUnifying s t
  unelab (Failed s) = pure $ Failed s

instance Unelab (AArgument ann) where
  type Unelabed (AArgument ann) = CArgument ann
  type UnelabEnv (AArgument ann) = Naming
  unelab (Argument mode desc term ann) = do
    term <- unelab term
    pure (Argument mode desc term ann)

instance Unelab (Trace ann AError (AStep ann)) where
  type Unelabed (Trace ann AError (AStep ann)) = Trace ann CError (CStep ann)
  type UnelabEnv (Trace ann AError (AStep ann)) = Naming
  unelab (Node a (em, s) ts) = case s of
    BindingStep (Variable r x) -> do
      na <- ask
      let y = freshen x na
      ts <- local (`nameOn` y) $ traverse unelab ts
      pure (Node a (BindingStep (Variable r y)) ts)
    NotedStep -> Node a NotedStep <$> traverse unelab ts
    PushingStep jd db (d, t) -> do
      jd <- subunelab jd
      v <- unelab db
      t <- unelab t
      Node a (PushingStep jd v (d, t)) <$> traverse unelab ts
    CallingStep jd tr -> do
      jd <- subunelab jd
      tr <- traverse unelab tr
      Node a (CallingStep jd tr) <$> traverse unelab ts
  unelab (Error a e) = Error a <$> unelab e

instance Pretty (CArgument ann) where
  pretty (Argument m _ t _) = withANSI [ SetColour Background (pick m) ] (pretty t) where

    pick :: Mode -> Colour
    pick Input = Blue
    pick Output = Red

instance Pretty (CStep ann) where
  pretty = \case
    BindingStep x -> withANSI [ SetColour Background Magenta ] ("\\" <> pretty x <> dot)
    PushingStep jd x (_, t) -> hsep [pretty jd, "|-", pretty x, "->", pretty t] <> dot
    CallingStep jd pts -> pretty jd <+> sep (pretty <$> pts)
    NotedStep -> ""

instance Pretty CError where
  pretty = \case
    StuckUnifying s t -> withANSI [ SetColour Background Yellow ]
                          (pretty s <+> "/~" <+> pretty t)
    Failed s -> withANSI [ SetColour Background Red ] (pretty s)

instance Pretty (Trace ann CError (CStep ann)) where
  pretty (Node _ i@(BindingStep x) ts) =
    let (prf, suf) = getPushes x ts in
    vcat ( hsep (pretty <$> i:prf) : map (indent 1 . pretty) suf)
  pretty (Node _ i ts) = vcat (pretty i : map (indent 1 . pretty) ts)
  pretty (Error _ e) = pretty e

instance LaTeX (CArgument ann) where
  type Format (CArgument ann) = ()
  toLaTeX _ (Argument _ d t _) = toLaTeX d t

instance LaTeX (CStep ann) where
  type Format (CStep ann) = ()
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
      pts <- traverse (toLaTeX ()) pts
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

instance LaTeX (Trace ann CError (CStep ann)) where
  type Format (Trace ann CError (CStep ann)) = ()
  toLaTeX n (Node _ i []) = do
    i <- toLaTeX () i
    pure $ call False "typosAxiom" [i]
  toLaTeX n (Node _ i@(BindingStep x) ts) = do
    let (prf, suf) = getPushes x ts
    i <- toLaTeX () i
    prf <- traverse (toLaTeX ()) prf
    suf <- traverse (toLaTeX ()) suf
    pure $ typosDerivation (i <> hsep (intersperse "\\ " prf)) suf

  toLaTeX n (Node _ i ts) = do
    i <- toLaTeX () i
    ts <- traverse (toLaTeX ()) ts
    pure $ typosDerivation i ts

  toLaTeX n (Error _ e) = do
    e <- toLaTeX () e
    pure $ call False "typosError" [e]

typosDerivation :: Doc () -> [Doc ()] -> Doc ()
typosDerivation i ts =
   call True "typosDerivation"
     [ i
     , vcat (call False "typosBeginPrems" []
            : intersperse (call False "typosBetweenPrems" []) ts
            ++ [call False "typosEndPrems" []])]

getPushes :: Variable -> [Trace ann CError (CStep ann)]
          -> ([CStep ann], [Trace ann CError (CStep ann)])
getPushes x [Node _ i@(PushingStep _ y _) ts] | x == y =
      let (prf, suf) = getPushes x ts in
      (i:prf, suf)
getPushes _ ts = ([], ts)

extract :: forall ann. ann -> [Frame] -> [Trace ann AError (AStep ann)]
extract a [] = []
extract a (f : fs) = case f of
  LeftBranch Hole p -> extract a fs ++ extract a (stack p) ++ findFailures p
  RightBranch p Hole -> extract a (stack p) ++ extract a fs ++ findFailures p
  Spawnee Interface{..} -> let p = snd spawner in
    Node a (extractionMode
            , CallingStep
               judgeName
               (zipWith toArgument judgeProtocol (traffic <>> [])))
               (extract a fs)
    : extract a (stack p) ++ findFailures p
  Spawner Interface{..} -> let p = fst spawnee in
    Node a (extractionMode
            , CallingStep
                judgeName
                (zipWith toArgument judgeProtocol (traffic <>> [])))
                (extract a (stack p)
                ++ findFailures p)
    : extract a fs
  Pushed jd (i, d, t) -> node (AlwaysExtract, PushingStep jd i (d, t))
  Binding x -> node (AlwaysExtract, BindingStep (Variable unknown x))
  UnificationProblem date s t -> Error a (StuckUnifying s t) : extract a fs
  Noted -> Node a (AlwaysExtract, NotedStep) [] : extract a fs
  _ -> extract a fs

  where
    toArgument :: (Mode, SyntaxDesc) -> Term -> AArgument ann
    toArgument (mode, desc) term = Argument mode desc term a

    findFailures :: Process Status [] -> [Trace ann AError (AStep ann)]
    findFailures p@Process{..}
     = case actor of
         Fail _ [StringPart e] -> [Error a (Failed e)]
         Fail _ _ -> error "Expected `Fail` message to be singleton string"
         _ -> []

    node :: AStep ann -> [Trace ann AError (AStep ann)]
    node s = [Node a s (extract a fs)]

cleanup :: [Trace ann AError (AStep ann)] -> [Trace ann AError (AStep ann)]
cleanup = snd . go False [] where

  go :: Bool            -- ^ is the parent suppressable?
     -> [JudgementForm] -- ^ list of toplevel judgements already seen
     -> [Trace ann AError (AStep ann)] -> (Any, [Trace ann AError (AStep ann)])
  go supp seen [] = pure []
  go supp seen (Node a (em, i@(CallingStep jd tr)) ts : ats)
    | em == InterestingExtract || jd `elem` seen
    = let (Any b, ts') = go True seen ts in
      if not supp && b
        then (Node a (em, i) ts' :) <$> go supp seen ats
        else (ts' ++) <$ tell (Any b) <*> go supp seen ats
    | em == TopLevelExtract
    = (:) <$> censor (const (Any False)) (Node a (em, i) <$> go False (jd : seen) ts)
          <*> go supp seen ats
    | otherwise
    = (:) <$> censor (const (Any False)) (Node a (em, i) <$> go False [] ts)
          <*> go supp seen ats
  go supp seen (Node a (em, NotedStep) _ : ats) = tell (Any True) >> go supp seen ats
  go supp seen (Node a i ts : ats) =
    (:) <$> censor (const (Any False)) (Node a i <$> go False seen ts)
        <*> go supp seen ats
  go supp seen (Error a e : ats) =
    (Error a e :) <$> go supp seen ats

diagnostic :: Options -> StoreF i -> [Frame] -> String
diagnostic opts st fs =
  let ats = cleanup $ extract () fs in
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
  let ats = cleanup $ extract () fs in
  let iats = instantiate st ats in
  let cts = traverse unelab iats in
  let rts = unsafeEvalUnelab initNaming cts in
  let dts = (`evalLaTeXM` table) (traverse (toLaTeX ()) rts) in
  show $ vcat $
   [ "\\documentclass[multi=page]{standalone}"
   , ""
   , "%%%%%%%%%%% Packages %%%%%%%%%%%%%%%%%%%"
   , "\\usepackage{xcolor}"
   , "\\usepackage{amsmath}"
   , "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
   , ""
   , "%%%%%%%%%%% Notations %%%%%%%%%%%%%%%%%%"
   , "\\newcommand{\\typosBinding}[1]{#1 \\vdash}"
   , "\\newcommand{\\typosPushing}[3]{\\textsc{#1} \\vdash #2 \\to #3.}"
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
