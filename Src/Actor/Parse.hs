module Actor.Parse where

import Control.Applicative
import Control.Monad

import qualified Data.Map as Map

import Hide
import Bwd
import Thin
import Term
import Pattern
import Actor

import Parse
import Term.Parse

pchan :: Parser Channel
pchan = Channel <$> pnom

pactorvar :: (ActorVar -> Parser a) -> Parser a
pactorvar p = do
  x <- pnom
  pmetasbind (Map.singleton x B0) $ p x

pmatchlabel :: Parser MatchLabel
pmatchlabel = id <$ pch ('/' ==) <*> pnom <|> pure ""

pactm :: Bwd Alias -> Parser (CdB (Tm ActorMeta))
pactm als = ((//^ subst als) . (fmap ActorVar $^)<$> plocal als ptm)  where

  subst :: Bwd Alias -> CdB (Sbst ActorMeta)
  subst B0 = sbst0 0
  subst (xz :< x) = subst xz `sbstT` ((Hide x :=) $^ (Alias x $: sbst0 0))

palias :: Bwd Alias -> Parser Alias
palias als = do
  x <- pnom
  guard (x `elem` als)
  pure x

pjudge :: Parser JudgementForm
pjudge = pnom

pextension :: Bwd Alias -> Parser (JudgementForm, MatchLabel, Alias, Actor)
pextension als =
  (,,,) <$> pjudge <* pch (== '/') <*> pnom
        <* punc "{" <*> palias als
        <* punc "->" <*> pACT als
        <* pspc <* pch (== '}')

pACT0 :: Parser Actor
pACT0 = pACT B0

pACT :: Bwd Alias -> Parser Actor
pACT als = pact als >>= more where

  more :: Actor -> Parser Actor
  more act = (act :|:) <$ punc "|" <*> pACT als
    <|> pure act

pclause :: Bwd Alias -> Parser (PatActor, Actor)
pclause als = do
  pat <- pactpat
  punc "->"
  xz <- pscope
  (pat,) <$> pmetasbind (bound xz pat) (pACT als)

pact :: Bwd Alias -> Parser Actor
pact als = id <$ pch (== '\\') <* pspc <*>
                 pactorvar (\ x -> Under x <$ punc "." <*> pact (als :< x))
  <|> Send <$> pchan <* punc "!" <*> pactm als <* punc "." <*> pact als
  <|> uncurry . Recv <$> pchan <* punc "?" <*> pactorvar (\ x -> (x,) <$ punc "." <*> pact als)
  <|> uncurry FreshMeta <$ pch (== '?') <* pspc <*> pactorvar (\ x -> (x,) <$ punc "." <*> pact als)
  <|> Spawn <$> pjudge <* punc "@" <*> pchan <* punc "." <*> pact als
  <|> Constrain <$> pactm als <* punc "~" <*> pactm als
  <|> Match <$ plit "case" <*> pmatchlabel <* pspc <*> pactm als <* punc "{"
       <*> psep (punc ";") (pclause als)
       <* pspc <* pch (== '}')
  <|> id <$ pch (== '(') <* pspc <*> pACT als <* pspc <* pch (== ')')
  <|> Break <$ plit "BREAK" <* pspc <*> pstring <* punc "." <*> pact als
  <|> Fail <$ pch (== '#') <* pspc <*> pstring
  <|> Extend <$> pextension als <* punc "." <*> pact als
  <|> pure Win

pactpat :: Parser PatActor
pactpat = fmap VarP <$> ppat
