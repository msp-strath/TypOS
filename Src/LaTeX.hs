{-# LANGUAGE OverloadedStrings #-}

module LaTeX where

import qualified Data.Map as Map
import Control.Monad.Reader

import Concrete.Base
import Doc
import Syntax
import Scope
import Hide (unhide)

import Unelaboration

newtype LaTeXM a = LaTeXM { runLaTeXM :: Reader SyntaxTable a }
  deriving (Functor, Applicative, Monad, MonadReader SyntaxTable)

evalLaTeXM :: LaTeXM a -> SyntaxTable -> a
evalLaTeXM ma table = (`runReader` table) $ runLaTeXM ma

class LaTeX a where
  type Format a
  toLaTeX :: Format a -> a -> LaTeXM (Doc ())

call :: Doc () -> [Doc ()] -> Doc ()
call d [] = backslash <> d
call d (x : xs) = call (d <> braces x) xs

instance LaTeX Variable where
  type Format Variable = ()
  toLaTeX _ (Variable str) = pure $ text str

asList :: Raw -> [Raw]
asList (At "") = []
asList (Cons p q) = p : asList q
asList p = [p]

toLaTeXCdr :: SyntaxDesc -> Raw -> LaTeXM (Doc ())
toLaTeXCdr _ (At "") = pure $ call "typosListEnd" []
toLaTeXCdr d (Cons p q) = do
  (dp, dq) <- ask >>= \ table -> pure $ case expand table d of
      Just (VCons dp dq) -> (dp, dq)
      Just (VNilOrCons dp dq) -> (dp, dq)
      _ -> (contract VWildcard, contract VWildcard)
  p <- toLaTeX dp p
  q <- toLaTeXCdr dq q
  pure $ p <+> q
toLaTeXCdr d p = do
  p <- toLaTeX d p
  pure $ call "typosListTail" [p]

instance LaTeX Raw where
  type Format Raw = SyntaxDesc
  toLaTeX d = \case
    Var v -> toLaTeX () v
    At "" -> pure $ call "typosNil" []
    At a -> ask >>= \ table -> pure $ case expand table d of
      Just VEnumOrTag{} -> call (text ("enum" ++ a)) [] -- as enum
      _ -> call "typosAtom" [text a] -- as atom
    Cons p q -> ask >>= \ table -> case expand table d of
      Just (VEnumOrTag _ ts) -> do
        let At a = p
        let Just ds = lookup a ts
        let qs = asList q
        call (text ("tag" ++ a)) <$> traverse (uncurry toLaTeX) (zip ds qs) -- as tags
      Just (VCons dp dq) -> do
        p <- toLaTeX dp p
        q <- toLaTeXCdr dq q
        pure $ call "typosListStart" [p, q]
      Just (VNilOrCons dp dq) ->  do
        p <- toLaTeX dp p
        q <- toLaTeXCdr dq q
        pure $ call "typosListStart" [p, q]
      _ -> do
        p <- toLaTeX (contract VWildcard) p
        q <- toLaTeXCdr (contract VWildcard) q
        pure $ call "typosListStart" [p, q]
    Lam (Scope x sc) -> do
      d <- ask >>= \ table -> pure $ case expand table d of
        Just (VBind s cb) -> cb
        _ -> contract VWildcard
      sc <- toLaTeX d sc
      pure $ call "typosScope" [text (unhide x), sc]
    Sbst bwd raw -> pure ""

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
  , "\\newcommand{\\typosListStart}[2]{[#1 #2}"
  , "\\newcommand{\\typosListEnd}{]}"
  , "\\newcommand{\\typosListTail}[1]{\\textbar #1]}"
  , "\\newcommand{\\typosScope}[2]{[\\textbackslash #1. #2]}"

  , "\\begin{document}"
  , show $ evalLaTeXM (toLaTeX syntaxT syntaxR) (Map.singleton "Syntax" syntaxT)
  , "\\end{document}"
  ]
