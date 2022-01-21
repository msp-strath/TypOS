module Actor.Parse where

import Control.Applicative
import Control.Monad

import Data.Set (Set)
import qualified Data.Set as Set

import Bwd
import Thin
import Term
import Pattern
import Actor

import Parse
import Term.Parse

pchan :: Parser Channel
pchan = Channel <$> pnom

pactorvar :: Parser ActorVar
pactorvar = pnom

pmatchlabel :: Parser MatchLabel
pmatchlabel = id <$ pch ('/' ==) <*> pnom <|> pure ""

pactm :: Set Alias -> Parser (CdB (Tm ActorMeta))
pactm als = (fmap adjust $^) <$> plocal B0 ptm where

  adjust :: String -> ActorMeta
  adjust str
    | str `Set.member` als = Alias str
    | otherwise = ActorVar str

palias :: Set Alias -> Parser Alias
palias als = do
  x <- pnom
  guard (x `Set.member` als)
  pure x

pjudge :: Parser JudgementForm
pjudge = pnom

pextension :: Set Alias -> Parser (JudgementForm, MatchLabel, Alias, Actor)
pextension als =
  (,,,) <$> pjudge <* pch (== '/') <*> pnom
        <* punc "{" <*> palias als
        <* punc "->" <*> pACT als
        <* pspc <* pch (== '}')

pACT0 :: Parser Actor
pACT0 = pACT Set.empty

pACT :: Set Alias -> Parser Actor
pACT als = pact als >>= more where

  more :: Actor -> Parser Actor
  more act = (act :|:) <$ punc "|" <*> pACT als
    <|> pure act

pact :: Set Alias -> Parser Actor
pact als = id <$ pch (== '\\') <* pspc <*> (do
    x <- pnom
    punc "."
    Under x <$> pact (Set.insert x als))
  <|> Send <$> pchan <* punc "!" <*> pactm als <* punc "." <*> pact als
  <|> Recv <$> pchan <* punc "?" <*> pactorvar <* punc "." <*> pact als
  <|> FreshMeta <$ pch (== '?') <* pspc <*> pactorvar <* punc "." <*> pact als
  <|> Spawn <$> pjudge <* punc "@" <*> pchan <* punc "." <*> pact als
  <|> Constrain <$> pactm als <* punc "~" <*> pactm als
  <|> Match <$ plit "case" <*> pmatchlabel <* pspc <*> pactm als <* punc "{"
       <*> psep (punc ";") ((,) <$> pactpat <* punc "->" <*> pACT als)
       <* pspc <* pch (== '}')
  <|> id <$ pch (== '(') <* pspc <*> pACT als <* pspc <* pch (== ')')
  <|> Break <$ plit "BREAK" <* pspc <*> pstring <* punc "." <*> pact als
  <|> Fail <$ pch (== '#') <* pspc <*> pstring
  <|> Extend <$> pextension als <* punc "." <*> pact als
  <|> pure Win

pactpat :: Parser PatActor
pactpat = fmap VarP <$> ppat

