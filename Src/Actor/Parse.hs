module Actor.Parse where

import Control.Applicative

import qualified Data.Map as Map

import Actor
import Bwd
import Hide
import Pattern
import Scope
import Term
import Thin

import Parse
import Term.Parse

pchan :: Parser Channel
pchan = Channel <$> pnom

pactorvar :: (ActorMeta -> Parser a) -> Parser a
pactorvar p = do
  x <- pnom
  pmetasbind (Map.singleton x B0) $ p (ActorMeta x)

pmatchlabel :: Parser MatchLabel
pmatchlabel = MatchLabel <$> poptional (id <$ pch ('/' ==) <*> pnom)

pactm :: Parser (CdB (Tm ActorMeta))
pactm = (fmap ActorMeta $^) <$> ptm

pjudge :: Parser JudgementForm
pjudge = pnom

pextension :: Parser (JudgementForm, MatchLabel, PatVar, Actor)
pextension =
  (,,,) <$> pjudge <*> (MatchLabel . Just <$ pch (== '/') <*> pnom)
        <* punc "{" <*> pvar error (pure . VarP)
        <* punc "->" <*> pACT
        <* pspc <* pch (== '}')

pACT :: Parser Actor
pACT = pact >>= more where

  more :: Actor -> Parser Actor
  more act = (act :|:) <$ punc "|" <*> pACT
    <|> pure act

pclause :: Parser (PatActor, Actor)
pclause = do
  pat <- pactpat
  punc "->"
  xz <- pscope
  (pat,) <$> pmetasbind (bound xz pat) pACT

pact :: Parser Actor
pact = id <$ pch (== '\\') <* pspc <*> (do
         x <- pnom
         punc "."
         Under . Scope (Hide x) <$> pbind x pact)
  <|> Send <$> pchan <* punc "!" <*> pactm <* punc "." <*> pact
  <|> uncurry . Recv <$> pchan <* punc "?" <*> pactorvar (\ x -> (x,) <$ punc "." <*> pact)
  <|> uncurry FreshMeta <$ pch (== '?') <* pspc <*> pactorvar (\ x -> (x,) <$ punc "." <*> pact)
  <|> Spawn <$> pjudge <* punc "@" <*> pchan <* punc "." <*> pact
  <|> Constrain <$> pactm <* punc "~" <*> pactm
  <|> Match <$ plit "case" <*> pmatchlabel <* pspc <*> pactm <* punc "{"
       <*> psep (punc ";") pclause
       <* pspc <* pch (== '}')
  <|> id <$ pch (== '(') <* pspc <*> pACT <* pspc <* pch (== ')')
  <|> Break <$ plit "BREAK" <* pspc <*> pstring <* punc "." <*> pact
  <|> Print <$ plit "PRINT" <* pspc <*> pargs [TermPart Instantiate ()] <* punc "." <*> pact
  <|> Print <$ plit "PRINTF" <* pspc <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Fail <$ pch (== '#') <* pspc <*> pstring
  <|> Extend <$> pextension <* punc "." <*> pact
  <|> pure Win

pformat :: Parser [FormatF Directive ()]
pformat = Parser $ \ env str -> case str of
  '"':str -> [go str B0]
  _ -> []

  where

  snoc :: String -> Bwd (FormatF Directive ()) -> Bwd (FormatF Directive ())
  snoc "" acc = acc
  -- hopefully there aren't too many of these
  snoc str (acc :< StringPart strl) = acc :< StringPart (strl ++ str)
  snoc str acc = acc :< StringPart str

  go :: String -> Bwd (FormatF Directive ()) -> ([FormatF Directive ()], String)
  go str acc = case span (`notElem` "%\"\\") str of
    (str, '%':'r':end) -> go end (snoc str acc :< TermPart Raw ())
    (str, '%':'i':end) -> go end (snoc str acc :< TermPart Instantiate ())
    (str, '\\':'n':end) -> go end (snoc (str ++ "\n") acc)
    (str, '\\':'t':end) -> go end (snoc (str ++ "\t") acc)
    (str, '\\':c:end) -> go end (snoc (str ++ [c]) acc)
    (str, '"':end)     -> (snoc str acc <>> [], end)
    (_, _) -> error "Unclosed format string"

pargs :: [FormatF Directive ()] -> Parser [FormatF Directive (CdB (Tm ActorMeta))]
pargs = traverse $ traverse (\ () -> id <$ pspc <*> pactm)

pactpat :: Parser PatActor
pactpat = fmap VarP <$> ppat
