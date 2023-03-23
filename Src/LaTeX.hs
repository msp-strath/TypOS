{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module LaTeX where

import Data.Char (isDigit)

import qualified Data.Map as Map
import Control.Monad.Reader

import Concrete.Base
import Text.PrettyPrint.Compact
import Hide
import Syntax
import Scope

import Unelaboration.Monad
import Unelaboration ()

newtype LaTeXM a = LaTeXM { runLaTeXM :: Reader SyntaxTable a }
  deriving (Functor, Applicative, Monad, MonadReader SyntaxTable)

evalLaTeXM :: LaTeXM a -> SyntaxTable -> a
evalLaTeXM ma table = (`runReader` table) $ runLaTeXM ma

class LaTeX a where
  type Format a
  toLaTeX :: Format a -> a -> LaTeXM (Doc ())

call :: Bool -> Doc () -> [Doc ()] -> Doc ()
call b d [] = backslash <> d
call b d (x : xs) = call b ((if b && not (null xs) then flush else id) (d <> braces x)) xs

spellOut :: Char -> String
spellOut '0' = "Zero"
spellOut '1' = "One"
spellOut '2' = "Two"
spellOut '3' = "Three"
spellOut '4' = "Four"
spellOut '5' = "Five"
spellOut '6' = "Six"
spellOut '7' = "Seven"
spellOut '8' = "Eight"
spellOut '9' = "Nine"
spellOut x = [x]

escapeLatex :: Char -> String
escapeLatex c | isDigit c = "Q" ++ spellOut c
escapeLatex '_' = "Qu"
escapeLatex '\'' = "Qp"
escapeLatex 'Q' = "QQ"
escapeLatex x = [x]


anEnum :: String -> String
anEnum e = "enum" ++ foldMap escapeLatex e

aTag :: String -> Int -> String
aTag t a = "tag" ++ foldMap escapeLatex t ++ "For" ++ foldMap spellOut (show a)

instance LaTeX x => LaTeX (Hide x) where
  type Format (Hide x) = Format x
  toLaTeX d (Hide x) = toLaTeX d x

instance LaTeX a => LaTeX (Binder a) where
  type Format (Binder a) = Format a
  toLaTeX d = \case
    Unused _ -> pure "\\_"
    Used x -> toLaTeX d x

instance LaTeX Variable where
  type Format Variable = ()
  toLaTeX _ (Variable _ ('_':cs)) = pure $ text ("\\_" ++ cs) -- hack for now
  toLaTeX _ (Variable _ ('?':'[':_)) = pure $ text ("???") -- hack for metas for now
  toLaTeX _ (Variable _ str) = pure $ text str

instance LaTeX String where
  type Format String = ()
  toLaTeX () s = pure $ text s

asList :: Raw -> [Raw]
asList (At _ "") = []
asList (Cons _ p q) = p : asList q
asList p = [p]

latexspace :: Doc ()
latexspace = "\\ "

toLaTeXCdr :: ASyntaxDesc -> Raw -> LaTeXM (Doc ())
toLaTeXCdr _ (At _ "") = pure $ call False "typosListEnd" []
toLaTeXCdr d (Cons _ p q) = do
  (dp, dq) <- ask >>= \ table -> pure $ case expand table d of
      Just (VCons dp dq) -> (dp, dq)
      Just (VNilOrCons dp dq) -> (dp, dq)
      _ -> (contract VWildcard, contract VWildcard)
  p <- toLaTeX dp p
  q <- toLaTeXCdr dq q
  pure $ latexspace <> p <> q
toLaTeXCdr d p = do
  p <- toLaTeX d p
  pure $ call False "typosListTail" [p]

instance LaTeX Raw where
  type Format Raw = SyntaxDesc
  toLaTeX d = \case
    Var _ v -> do
      v <- toLaTeX () v
      pure $ call False "mathit" [v]
    At _ "" -> pure $ call False "typosNil" []
    At _ a -> ask >>= \ table -> pure $ case expand table d of
      Just VEnumOrTag{} -> call False (text (anEnum a)) [] -- as enum
      _ -> call False "typosAtom" [text a] -- as atom
    Cons _ p q -> ask >>= \ table -> case expand table d of
      Just (VEnumOrTag _ ts) -> do
        let At _ a = p
        let Just ds = lookup a ts
        let qs = asList q
        call False (text (aTag a (length ds))) <$> traverse (uncurry toLaTeX) (zip ds qs) -- as tags
      Just (VCons dp dq) -> do
        p <- toLaTeX dp p
        q <- toLaTeXCdr dq q
        pure $ call False "typosListStart" [p, q]
      Just (VNilOrCons dp dq) ->  do
        p <- toLaTeX dp p
        q <- toLaTeXCdr dq q
        pure $ call False "typosListStart" [p, q]
      _ -> do
        p <- toLaTeX (contract VWildcard) p
        q <- toLaTeXCdr (contract VWildcard) q
        pure $ call False "typosListStart" [p, q]
    Lam _ (Scope x sc) -> do
      d <- ask >>= \ table -> pure $ case expand table d of
        Just (VBind s cb) -> cb
        _ -> contract VWildcard
      sc <- toLaTeX d sc
      bd <- toLaTeX () x
      pure $ call False "typosScope" [bd, sc]
    Sbst _ bwd raw -> pure ""

test =
  putStrLn $
  let syntaxT = syntaxDesc ["Syntax"] in
  let syntaxR = unsafeEvalUnelab initNaming (unelab syntaxT) in
  unlines
  [ "\\documentclass{article}"

  , "\\newcommand{\\tagEnumOrTag}[2]{['EnumOrTag #1 #2]}"
  , "\\newcommand{\\tagFix}[1]{['Fix #1]}"
  , "\\newcommand{\\tagCons}[2]{['Cons #1 #2]}"
  , "\\newcommand{\\tagNilOrCons}[2]{['NilOrCons #1 #2]}"
  , "\\newcommand{\\tagBind}[2]{['Bind #1 #2]}"

  , "\\newcommand{\\enumAtom}{'Atom}"
  , "\\newcommand{\\enumSyntax}{'Syntax}"

  , "\\newcommand{\\typosAtom}[1]{'#1}"
  , "\\newcommand{\\typosNil}{[]}"
  , "\\newcommand{\\typosListStart}[2]{[#1#2}"
  , "\\newcommand{\\typosListEnd}{]}"
  , "\\newcommand{\\typosListTail}[1]{\\textbar #1]}"
  , "\\newcommand{\\typosScope}[2]{[\\textbackslash #1. #2]}"

  , "\\begin{document}"
  , render $ evalLaTeXM (toLaTeX syntaxT syntaxR) (Map.singleton "Syntax" syntaxT)
  , "\\end{document}"
  ]
