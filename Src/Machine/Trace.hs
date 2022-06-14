{-# LANGUAGE OverloadedStrings, UndecidableInstances, ScopedTypeVariables, RankNTypes #-}
module Machine.Trace where

import Control.Monad.Reader
import Control.Monad.Writer

import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable

import Data.List (intersperse, elemIndex, groupBy, sortBy)
import Data.Function (on)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)

import ANSI (Colour(..), Layer(..), Annotation(..))
import Actor (JudgementForm)
import Bwd (Bwd(..), (<>>), (<><))
import Concrete.Base
import Concrete.Pretty()
import Doc hiding (render)
import Doc.Render.Terminal
import Format
import LaTeX
import Location (unknown)
import Machine.Base
import Machine.Display
import Options
import Pretty
import Syntax (SyntaxDesc, SyntaxTable, expand, VSyntaxDesc (..), contract)
import Term.Base
import Unelaboration
import Data.String (fromString)
import Data.Functor ((<&>))

data Trace e i ann
   = Node ann (i ann) [Trace e i ann]
   | Error ann e

deriving instance Functor i => Functor (Trace e i)
deriving instance Foldable i => Foldable (Trace e i)

instance (Show e, Show (i ann)) => Show (Trace e i ann) where
  show = unlines . go "" where

    go indt (Node _ i ts) = (indt ++ show i) : concatMap (go (' ':indt)) ts
    go indt (Error _ e)   = [indt ++ show e]

type family ITERM (ph :: Phase) :: *
type instance ITERM Abstract = Term
type instance ITERM Concrete = Raw

data ARGUMENT (ph :: Phase) f ann = Argument
  { argMode :: Mode
  , argDesc :: SyntaxDesc
  , argTerm :: f (ITERM ph) ann
  }

deriving instance
  ( Show (f (ITERM ph) ann)
  ) => Show (ARGUMENT ph f ann)

deriving instance
  ( Functor (f (ITERM ph))
  ) => Functor (ARGUMENT ph f)

deriving instance
  ( Foldable (f (ITERM ph))
  ) => Foldable (ARGUMENT ph f)

type AArgument = ARGUMENT Abstract
type CArgument = ARGUMENT Concrete

instance Bifunctor f => Instantiable (AArgument f ann) where
  type Instantiated (AArgument f ann) = AArgument f ann
  instantiate st (Argument mode desc term)
    = Argument mode desc (first (instantiate st) term)

data STEP (ph :: Phase) f ann
  = BindingStep Variable
  | NotedStep
  | PushingStep (STACK ph) (TERMVAR ph) (SyntaxDesc, f (ITERM ph) ann)
  | CallingStep (f () (ann, Bool)) (JUDGEMENTFORM ph) [ARGUMENT ph f ann]

deriving instance
  ( Functor (f (ITERM ph))
  , Functor (f ())
  ) => Functor (STEP ph f)

deriving instance
  ( Foldable (f (ITERM ph))
  , Foldable (f ())
  ) => Foldable (STEP ph f)

data AStep f ann = AStep ExtractMode (STEP Abstract f ann)
type CStep f = STEP Concrete f

deriving instance
  ( Functor (f Term)
  , Functor (f ())
  ) => Functor (AStep f)

deriving instance
  ( Foldable (f Term)
  , Foldable (f ())
  ) => Foldable (AStep f)

instance Bifunctor f => Instantiable1 (AStep f) where
  type Instantiated1 (AStep f) = AStep f
  instantiate1 st (AStep em step) = AStep em $ case step of
    BindingStep x -> BindingStep x
    NotedStep -> NotedStep
    PushingStep jd db t -> PushingStep jd db (first (instantiate st) <$> t)
    CallingStep b jd tr -> CallingStep b jd (instantiate st <$> tr)

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

type CTrace f ann = Trace CError (CStep f) ann
type ATrace f ann = Trace AError (AStep f) ann

data Simple t ann = Simple t ann
newtype Series t ann = Series { runSeries :: [(t, ann)] }

mkSeries :: t -> ann -> Series t ann
mkSeries t a = Series [(t, a)]

instance Bifunctor Simple where
  bimap f g (Simple t a) = Simple (f t) (g a)

instance Bifoldable Simple where
  bifoldr f g n (Simple t a) = f t $ g a n

instance Bitraversable Simple where
  bitraverse f g (Simple t a) = Simple <$> f t <*> g a

instance Pretty t => Pretty (Simple t ()) where
  pretty (Simple t _) = pretty t

instance LaTeX t => LaTeX (Simple t ()) where
  type Format (Simple t ()) = LaTeX.Format t
  toLaTeX d (Simple t _) = toLaTeX d t

instance LaTeX (Simple () (a, Bool)) where
  type Format (Simple () (a, Bool)) = ()
  toLaTeX d (Simple _ (_, b)) = pure $ if b then call False "typosCheckmark" [] else mempty

instance LaTeX (Series () (Int, Bool)) where
  type Format (Series () (Int, Bool)) = ()
  toLaTeX d (Series ibs)
    = do let ibss = groupBy ((==) `on` fst) $ sortBy (compare `on` snd) $ map snd ibs
         (ibss, ibs) <- case B0 <>< ibss of
                          ibz :< ibs -> pure (ibz <>> [], ibs)
                          -- Famous last words: trust me that's the only case
         let doc = display1 ibs
         let docs = ibss <&> \ tns -> call False "mathrlap" [display1 tns]
         pure $ vcat (docs ++ [doc])

      where
        display1 :: [(Int, Bool)] -> Doc ()
        display1 ibs@((_, b) : _) | b = do
          let ns = map fst ibs
          let start = minimum ns
          let end = maximum ns
          let only = concat ["uncover<", show start, "-", show end, ">"]
          call False (fromString only) [call False "typosCheckmark" []]
        display1 _ = ""

instance Functor (Series t) where
  fmap = second

instance Foldable (Series t) where
  foldr = bifoldr (flip const)

instance Bifunctor Series where
  bimap f g = Series . map (bimap f g) . runSeries

instance Bifoldable Series where
  bifoldr f g n (Series tanns) = foldr (flip $ bifoldr f g) n tanns

instance Bitraversable Series where
  bitraverse f g (Series tanns) = Series <$> traverse (bitraverse f g) tanns

instance (Eq t, LaTeX t) => LaTeX (Series t Int) where
  type Format (Series t Int) = LaTeX.Format t
  toLaTeX d (Series tanns)
    = do let tnss = groupBy ((==) `on` fst) $ sortBy (compare `on` snd) tanns
         (tnss, tns) <- case B0 <>< tnss of
                          tnz :< tns -> pure (tnz <>> [], tns)
                          -- Famous last words: trust me that's the only case
         doc <- display1 tns
         docs <- flip traverse tnss $ \ tns -> do
                   doc <- display1 tns
                   pure $ call False "mathrlap" [doc]
         pure $ vcat (docs ++ [doc])

      where
        display1 :: [(t, Int)] -> LaTeXM (Doc ())
        display1 tns@((t, _) : _) = do
          let ns = map snd tns
          let start = minimum ns
          let end = maximum ns
          let only = concat ["uncover<", show start, "-", show end, ">"]
          doc <- toLaTeX d t
          pure $ call False (fromString only) [doc]

type Shot = [ATrace Simple Int]
type Shots = [Shot]

instance (Instantiable e, Instantiable1 i) => Instantiable (Trace e i ann) where
  type Instantiated (Trace e i ann) = Trace (Instantiated e) (Instantiated1 i) ann
  instantiate st (Node a i ts) = Node a (instantiate1 st i) (instantiate st <$> ts)
  instantiate st (Error a e)   = Error a (instantiate st e)

instance Unelab AError where
  type Unelabed AError = CError
  type UnelabEnv AError = Naming
  unelab (StuckUnifying s t) = do
    s <- unelab s
    t <- unelab t
    pure $ StuckUnifying s t
  unelab (Failed s) = pure $ Failed s

instance Bitraversable f => Unelab (AArgument f ann) where
  type Unelabed (AArgument f ann) = CArgument f ann
  type UnelabEnv (AArgument f ann) = Naming
  unelab (Argument mode desc term) = do
    term <- bitraverse unelab pure term
    pure (Argument mode desc term)

instance Bitraversable f => Unelab (ATrace f ann) where
  type Unelabed (ATrace f ann) = CTrace f ann
  type UnelabEnv (ATrace f ann) = Naming
  unelab (Node a (AStep em s) ts) = case s of
    BindingStep (Variable r x) -> do
      na <- ask
      let y = freshen x na
      ts <- local (`nameOn` y) $ traverse unelab ts
      pure (Node a (BindingStep (Variable r y)) ts)
    NotedStep -> Node a NotedStep <$> traverse unelab ts
    PushingStep jd db (d, t) -> do
      jd <- subunelab jd
      v <- unelab db
      t <- bitraverse unelab pure t
      Node a (PushingStep jd v (d, t)) <$> traverse unelab ts
    CallingStep b jd tr -> do
      jd <- subunelab jd
      tr <- traverse unelab tr
      Node a (CallingStep b jd tr) <$> traverse unelab ts
  unelab (Error a e) = Error a <$> unelab e

instance Pretty (CArgument Simple ()) where
  pretty (Argument m _ t) = withANSI [ SetColour Background (pick m) ] (pretty t) where

    pick :: Mode -> Colour
    pick Input = Blue
    pick Output = Red

instance Pretty (CStep Simple ()) where
  pretty = \case
    BindingStep x -> withANSI [ SetColour Background Magenta ] ("\\" <> pretty x <> dot)
    PushingStep jd x (_, t) -> hsep [pretty jd, "|-", pretty x, "->", pretty t] <> dot
    CallingStep (Simple () (_, b)) jd pts ->
      withANSI [ SetColour Background (if b then Green else Yellow) ] (pretty jd)
      <+> sep (pretty <$> pts)
    NotedStep -> ""

instance Pretty CError where
  pretty = \case
    StuckUnifying s t -> withANSI [ SetColour Background Yellow ]
                          (pretty s <+> "/~" <+> pretty t)
    Failed s -> withANSI [ SetColour Background Red ] (pretty s)

instance Pretty (CTrace Simple ()) where
  pretty (Node _ i@(BindingStep x) ts) =
    let (prf, suf) = getPushes x ts in
    vcat ( hsep (pretty <$> i:prf) : map (indent 1 . pretty) suf)
  pretty (Node _ i ts) = vcat (pretty i : map (indent 1 . pretty) ts)
  pretty (Error _ e) = pretty e

class AnnotateLaTeX ann where
  annotateLaTeX :: ann -> Doc () -> Doc ()

instance AnnotateLaTeX () where
  annotateLaTeX _ = id

instance AnnotateLaTeX Int where
  annotateLaTeX n d = call False (fromString ("visible<" ++ show n ++ "->")) [d]

instance (LaTeX (f Raw ann), LaTeX.Format (f Raw ann) ~ SyntaxDesc) =>
         LaTeX (CArgument f ann) where
  type Format (CArgument f ann) = ()
  toLaTeX _ (Argument m d t) = do
    t <- toLaTeX d t
    pure $ call False (fromString $ "typos" ++ show m) [t]

instance ( LaTeX (f Raw ann), LaTeX.Format (f Raw ann) ~ SyntaxDesc
         , LaTeX (f () (ann, Bool)), LaTeX.Format (f () (ann, Bool)) ~ ()) =>
         LaTeX (CStep f ann) where
  type Format (CStep f ann) = ()
  toLaTeX _ = \case
    BindingStep x -> do
      x <- toLaTeX () x
      pure $ call False "typosBinding" [x]
    PushingStep jd x (d, t) -> do
      jd <- toLaTeX () jd
      x <- toLaTeX () x
      t <- toLaTeX d t
      pure $ call False "typosPushing" [jd, x, t]
    CallingStep b jd pts -> do
      b <- toLaTeX () b
      jd <- toLaTeX () jd
      pts <- traverse (toLaTeX ()) pts
      pure $ call False ("calling" <> jd) pts <+> b
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

instance ( LaTeX (f Raw ann), LaTeX.Format (f Raw ann) ~ SyntaxDesc
         , LaTeX (f () (ann, Bool)), LaTeX.Format (f () (ann, Bool)) ~ ()
         , AnnotateLaTeX ann) => LaTeX (CTrace f ann) where
  type Format (CTrace f ann) = ()
  toLaTeX n (Node ann i []) = do
    i <- toLaTeX () i
    pure $ annotateLaTeX ann $ call False "typosAxiom" [i]
  toLaTeX n (Node ann i@(BindingStep x) ts) = do
    let (prf, suf) = getPushes x ts
    i <- toLaTeX () i
    prf <- traverse (toLaTeX ()) prf
    suf <- traverse (toLaTeX ()) suf
    pure $ annotateLaTeX ann $ typosDerivation (i <> hsep (intersperse "\\ " prf)) suf

  toLaTeX n (Node ann i ts) = do
    i <- toLaTeX () i
    ts <- traverse (toLaTeX ()) ts
    pure $ annotateLaTeX ann $ typosDerivation i ts

  toLaTeX n (Error ann e) = do
    e <- toLaTeX () e
    pure $ annotateLaTeX ann $ call False "typosError" [e]

typosDerivation :: Doc () -> [Doc ()] -> Doc ()
typosDerivation i ts =
   call True "typosDerivation"
     [ i
     , vcat (call False "typosBeginPrems" []
            : intersperse (call False "typosBetweenPrems" []) ts
            ++ [call False "typosEndPrems" []])]

getPushes :: Variable -> [CTrace f ann]
          -> ([CStep f ann], [CTrace f ann])
getPushes x [Node _ i@(PushingStep _ y _) ts] | x == y =
      let (prf, suf) = getPushes x ts in
      (i:prf, suf)
getPushes _ ts = ([], ts)

extract :: forall f ann. (forall t ann. t -> ann -> f t ann) -> ann -> [Frame] -> [ATrace f ann]
extract mkF a = go where
  go :: [Frame] -> [ATrace f ann]
  go [] = []
  go (f : fs) = case f of
    LeftBranch Hole p -> go fs ++ go (stack p) ++ findFailures p
    RightBranch p Hole -> go (stack p) ++ go fs ++ findFailures p
    Spawnee Interface{..} -> let p = snd spawner in
      Node a (AStep extractionMode
             $ CallingStep  (mkF () (a, isDone (store p)))
                 judgeName
                 (zipWith toArgument judgeProtocol (traffic <>> [])))
                 (go fs)
      : go (stack p) ++ findFailures p
    Spawner Interface{..} -> let p = fst spawnee in
      Node a (AStep extractionMode
             $ CallingStep (mkF () (a, isDone (store p)))
                  judgeName
                  (zipWith toArgument judgeProtocol (traffic <>> [])))
                  (go (stack p)
                  ++ findFailures p)
      : go fs
    Pushed jd (i, d, t) -> node fs (AStep AlwaysExtract $ PushingStep jd i (d, mkF t a))
    Binding x -> node fs (AStep AlwaysExtract $ BindingStep (Variable unknown x))
    UnificationProblem date s t -> Error a (StuckUnifying s t) : go fs
    Noted -> Node a (AStep AlwaysExtract NotedStep) [] : go fs
    _ -> go fs

  toArgument :: (Mode, SyntaxDesc) -> Term -> AArgument f ann
  toArgument (mode, desc) term = Argument mode desc (mkF term a)

  findFailures :: Process log Status [] -> [ATrace f ann]
  findFailures p@Process{..}
   = case actor of
       Fail _ [StringPart e] -> [Error a (Failed e)]
       Fail _ _ -> error "Expected `Fail` message to be singleton string"
       _ -> []

  node :: [Frame] -> AStep f ann -> [ATrace f ann]
  node fs s = [Node a s (go fs)]

cleanup :: [ATrace f ann] -> [ATrace f ann]
cleanup = snd . go False [] where

  go :: Bool            -- ^ is the parent suppressable?
     -> [JudgementForm] -- ^ list of toplevel judgements already seen
     -> [ATrace f ann] -> (Any, [ATrace f ann])
  go supp seen [] = pure []
  go supp seen (Node a (AStep em i@(CallingStep b jd tr)) ts : ats)
    | em == InterestingExtract || jd `elem` seen
    = let (Any b, ts') = go True seen ts in
      if not supp && b
        then (Node a (AStep em i) ts' :) <$> go supp seen ats
        else (ts' ++) <$ tell (Any b) <*> go supp seen ats
    | em == TopLevelExtract
    = (:) <$> censor (const (Any False)) (Node a (AStep em i) <$> go False (jd : seen) ts)
          <*> go supp seen ats
    | otherwise
    = (:) <$> censor (const (Any False)) (Node a (AStep em i) <$> go False [] ts)
          <*> go supp seen ats
  go supp seen (Node a (AStep em NotedStep) _ : ats) = tell (Any True) >> go supp seen ats
  go supp seen (Node a i ts : ats) =
    (:) <$> censor (const (Any False)) (Node a i <$> go False seen ts)
        <*> go supp seen ats
  go supp seen (Error a e : ats) =
    (Error a e :) <$> go supp seen ats

diagnostic :: Options -> StoreF i -> [Frame] -> String
diagnostic opts st fs =
  let ats = cleanup $ extract Simple () fs in
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

syntaxPreamble :: SyntaxTable -> [Doc ()]
syntaxPreamble table = concatMap (pure . render)
                                 (foldMap extract (Map.elems table))
  where

  extract :: SyntaxDesc -> Set.Set (Either String (String, Int))
  extract desc = case Syntax.expand Map.empty desc of
    Just (VCons d e) -> extract d <> extract e
    Just (VEnumOrTag es tds) ->
        foldMap (Set.singleton . Left) es <>
        foldMap (Set.singleton . Right . second length) tds
    _ -> mempty

  render :: Either String (String, Int) -> Doc ()
  render (Left e)      = text $ mkNewCommand (anEnum e) 0 (mkTag e)
  render (Right (t,a)) = text $ mkNewCommand (aTag t a) a
                              $ unwords ("[" : mkTag t : nArgs a ++ ["]"])


judgementPreamble :: Frame -> [Doc ()]
judgementPreamble (Rules jd jp _)
  = [text $ mkNewCommand ("calling" ++ jd) (length jp)
          $ "\\textsc{" ++ jd ++ "}" ++ unwords (nArgs (length jp))
    ]
judgementPreamble _ = []

ldiagnostic :: SyntaxTable -> StoreF i -> [Frame] -> String
ldiagnostic table st fs =
  let ats = cleanup $ extract Simple () fs in
  let iats = instantiate st ats in
  ldiagnostic' standalone table fs iats

adiagnostic :: SyntaxTable -> Store -> [Frame] -> Shots -> String
adiagnostic table st fs trs =
  let ats = cleanup $ combines (instantiate st $ extract mkSeries (length trs) fs) trs in
  -- The cleanup will have removed frames that are not notable and so there will be
  -- gaps in the numbered frames.
  -- The parallel top-level derivations also all share the same counter and so later
  -- derivations will not start counting at zero.
  let res = ats <&> \ at ->
        -- This bit of magic:
        -- 1. collects all the leftover numbers in the given derivation and sorts them
        let as = Set.toList $ foldMap Set.singleton at in
        -- 2. remaps them to an initial [1..n] segment by replacing each number i
        --    with its position in the sorted array.
        fmap (\ i -> fromMaybe (error "Impossible") (elemIndex i as)) at
  -- we can now render the beamer
  in ldiagnostic' beamer table fs res

data LaTeXConfig = LaTeXConfig
  { documentClass :: String
  , beginPage :: String
  , endPage :: String
  }

standalone :: LaTeXConfig
standalone = LaTeXConfig
  { documentClass = "\\documentclass[multi=page]{standalone}"
  , beginPage = "\\begin{page}"
  , endPage = "\\end{page}"
  }

beamer :: LaTeXConfig
beamer = LaTeXConfig
  { documentClass = unlines [ "\\documentclass{beamer}"
                            , "\\setbeamertemplate{navigation symbols}{}"
                            ]
  , beginPage = "\\begin{frame}[fragile]"
  , endPage = "\\end{frame}"
  }

ldiagnostic' :: AnnotateLaTeX ann
             => Bitraversable f
             => LaTeX (f Raw ann)
             => LaTeX.Format (f Raw ann) ~ SyntaxDesc
             => LaTeX (f () (ann, Bool))
             => LaTeX.Format (f () (ann, Bool)) ~ ()
             => LaTeXConfig
             -> SyntaxTable
             -> [Frame]
             -> [ATrace f ann]
             -> String
ldiagnostic' cfg table fs ats =
  let cts = traverse unelab ats in
  let rts = unsafeEvalUnelab initNaming cts in
  let dts = (`evalLaTeXM` table) (traverse (toLaTeX ()) rts) in
  show $ vcat $
   [ fromString (documentClass cfg)
   , ""
   , "%%%%%%%%%%% Packages %%%%%%%%%%%%%%%%%%%"
   , "\\usepackage{xcolor}"
   , "\\usepackage{amsmath}"
   , "\\usepackage{amssymb}"
   , "\\usepackage{mathtools}"
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
   , "\\newcommand{\\typosInput}[1]{\\textcolor{blue}{#1}}"
   , "\\newcommand{\\typosOutput}[1]{\\textcolor{red}{#1}}"
   , "\\newcommand{\\typosCheckmark}{^\\checkmark}"
   , "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
   , ""
   ] ++
   syntaxPreamble table
   ++ concatMap judgementPreamble fs
   ++
   [ "%\\input{notations}"
   , ""
   , "%%%%%%%%%%% Derivations %%%%%%%%%%%%%%%%"
   , "\\begin{document}"
   ] ++
   (dts >>= \ der ->
      [ fromString (beginPage cfg)
      , "$\\displaystyle"
      , "\\begin{array}{l}"
      , der
      , "\\end{array}"
      , "$"
      , fromString (endPage cfg)
      , "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
      , ""
      ]) ++
   [ "\\end{document}"]

combineWith :: (a -> b -> b) -> [a] -> [b] -> [b]
combineWith f [] bs = bs
combineWith f (a:as) (b:bs) = f a b : combineWith f as bs
combineWith f _ _ = error "Impossible"

cons :: Simple t ann -> Series t ann -> Series t ann
cons (Simple t ann) (Series tanns) = Series ((t, ann) : tanns)

combineArg :: ARGUMENT ph Simple ann
           -> ARGUMENT ph Series ann
           -> ARGUMENT ph Series ann
combineArg (Argument mode0 desc0 term0) (Argument mode1 desc1 term1)
  | (mode0, desc0) == (mode1, desc1)
  = Argument mode1 desc1 (cons term0 term1)
  | otherwise = error "Impossible"

combineStep :: Eq (STACK ph)
            => Eq (JUDGEMENTFORM ph)
            => Eq (TERMVAR ph)
            => STEP ph Simple ann
            -> STEP ph Series ann
            -> STEP ph Series ann
combineStep (BindingStep vari) stps@(BindingStep varj)
  | vari == varj = stps
combineStep NotedStep NotedStep = NotedStep
combineStep (PushingStep st0 ter0 (d0, x0)) (PushingStep st1 ter1 (d1, x1))
  | (st0, ter0, d0) == (st1, ter1, d1) = PushingStep st1 ter1 (d0, cons x0 x1)
combineStep (CallingStep b0 judge0 ars0) (CallingStep b1 judge1 ars1)
  | judge0 == judge1
  = CallingStep (cons b0 b1) judge0 (combineWith combineArg ars0 ars1)
combineStep _ _ = error "Impossible"

combine :: Ord ann
        => Trace e (AStep Simple) ann
        -> Trace e (AStep Series) ann
        -> Trace e (AStep Series) ann
combine (Node a0 (AStep _ stp) trs) (Node a1 (AStep em stps) trss)
  = Node (min a0 a1) (AStep em $ combineStep stp stps) (combineWith combine trs trss)
combine (Error a0 _) (Error a1 err) = Error (min a0 a1) err
combine (Error _ _) t = t
combine _ _ = error "Impossible"

combines :: Ord ann
         => [Trace e (AStep Series) ann]
         -> [[Trace e (AStep Simple) ann]]
         -> [Trace e (AStep Series) ann]
combines = foldr (combineWith combine)
