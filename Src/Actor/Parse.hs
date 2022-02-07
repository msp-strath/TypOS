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
pmatchlabel = id <$ pch ('/' ==) <*> pnom <|> pure ""

pactm :: Parser (CdB (Tm ActorMeta))
pactm = (fmap ActorMeta $^) <$> ptm

pjudge :: Parser JudgementForm
pjudge = pnom

pextension :: Parser (JudgementForm, MatchLabel, PatVar, Actor)
pextension =
  (,,,) <$> pjudge <* pch (== '/') <*> pnom
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
  <|> Fail <$ pch (== '#') <* pspc <*> pstring
  <|> Extend <$> pextension <* punc "." <*> pact
  <|> pure Win

pactpat :: Parser PatActor
pactpat = fmap VarP <$> ppat
