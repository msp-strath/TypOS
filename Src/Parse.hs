module Parse where

import Control.Applicative
import Control.Monad
import Data.Char

import Data.Set (Set)
import qualified Data.Set as Set

import Hide
import Bwd
import Thin
import Term
import Actor

-- parsers, by convention, do not consume either leading
-- or trailing space

class Lisp t where
  mkNil  :: Int -> t
  mkCons :: t -> t -> t
  pCar   :: Parser t

instance Lisp (CdB (Tm String)) where
  mkNil = atom ""
  mkCons = (%)
  pCar = ptm

instance Lisp Pat where
  mkNil = const (AP "")
  mkCons = PP
  pCar = ppat

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

plit :: String -> Parser ()
plit = mapM_ (pch . (==))

punc :: String -> Parser ()
punc cs = () <$ pspc <* plit cs <* pspc

pstring :: Parser String
pstring = Parser $ \ xz str -> case str of
  '"' : str -> case span ('"' /=) str of
    (str, _:end) -> pure (str, end)
    _ -> []
  _ -> []

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

pnat :: Parser Int
pnat = Parser $ \ xz str -> case span isDigit str of
  (ds@(_:_), str) -> [(read ds, str)]
  _ -> []

pvar' :: Parser (String, Int)
pvar' = (,) <$> pnom <*> ((id <$ pch (== '^') <*> pnat) <|> pure 0)

pvar :: (String -> Parser a) -> (Int -> Parser a) -> Parser a
pvar str int = (either str int <=< pseek) =<< pvar'

pactpat :: Parser PatActor
pactpat = fmap VarP <$> ppat

ppat :: Parser Pat
ppat = pvar (\ str -> MP str . ones <$> plen) (pure . VP)
  <|> AP <$ pch (== '\'') <*> pnom
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ppat <* pspc <* pch (== ')')
  <|> id <$ pch (== '\\') <* pspc <*> (do
    x <- pnom
    pspc
    pch (== '.')
    pspc
    (BP (Hide x)) <$> (pbind x ppat))
  <|> id <$ pch (== '{') <* pspc <*> do
    (th, xz) <- pth
    pspc
    (*^ th) <$> plocal xz ppat

ptm :: Parser (CdB (Tm String))
ptm = pvar (\ str -> (str $:) . sbstI <$> plen) (\ i -> var i <$> plen)
  <|> atom <$ pch (== '\'') <*> pnom <*> plen
  <|> id <$ pch (== '\\') <* pspc <*> (do
    x <- pnom
    pspc
    pch (== '.')
    pspc
    (x \\) <$> (pbind x ptm))
  <|> glomQlist <$> plen <* pch (== '\'') <* pch (== '[') <* pspc <*> many (ptm <* pspc) <* pch (== ']')
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ptm <* pspc <* pch (== ')')
  <|> id <$ pch (== '{') <* pspc <*> do
    (sg, xz) <- psbst
    pspc
    (//^ sg) <$> plocal xz ptm
  where
    glomQlist l = foldr qc qn where
      qc a d = ("Cons",l) #% [a, d]
      qn = ("Nil",l) #% []

pth :: Parser (Th, Bwd String)
pth = do
  (xns, b) <- raw
  xz <- pscope
  let xnz = deBruijnify xz
  let th = (if b then comp else id) (which (`elem` xns) xnz)
  pure (th, th ^? xz)

  where

  raw :: Parser ([(String, Int)], Bool)
  raw = (,) <$> many (id <$ pspc <*> pvar') <* pspc
            <*> (True <$ pch (== '*') <|> pure False)
            <* pspc <* pch (== '}')

psbst :: Parser (CdB (Sbst String), Bwd String)
psbst = (,) <$ pspc <* pch (== '}') <*> (sbstI <$> plen) <*> pscope
  <|> id <$ pch (== ',') <* pspc <*> psbst
  <|> (pnom >>= \ x -> pspc >> ppop x psbst >>= \ (sg, xz) ->
       pure (sbstW sg (ones 1), xz :< x))
  <|> (pnom >>= \ x -> pch (== '*') >> ppop x psbst >>= \ (sg, xz) ->
       pure (sbstW sg (none 1), xz))
  <|> do
    x <- pnom
    pspc ; pch (== '=') ; pspc
    (t, th) <- ptm
    (sg, xz) <- psbst
    return (sbstT sg ((Hide x := t), th), xz :< x)

plisp :: Lisp t => Parser t
plisp = mkNil <$ pch (== ']') <*> plen
    <|> id <$ pch (== '|') <* pspc <*> pCar <* pspc <* pch (== ']')
    <|> mkCons <$> pCar <* pspc <*> plisp

pnom :: Parser String
pnom = Parser $
  let isMo c = isAlphaNum c || elem c "_'" in
  \ xz str -> case str of
  c : cs | isAlpha c -> case span isMo cs of
      (nm, str) -> [(c:nm, str)]
  _ -> []


pspc :: Parser ()
pspc = Parser $ \ xs str -> [((),snd (span isSpace str))]

pnl :: Parser ()
pnl = () <$ pch (\c -> c == '\n' || c == '\0')

psep :: Parser () -> Parser a -> Parser [a]
psep s p = (:) <$> p <*> many (id <$ s <*> p)
 <|> pure []

data Parser a = Parser
  { parser :: Bwd String -> String -> [(a, String)]
  }

instance Monad Parser where
  return a = Parser $ \ xz s -> [(a, s)]
  Parser f >>= k = Parser $ \ xz s -> do
    (a, s) <- f xz s
    parser (k a) xz s

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Functor Parser where
  fmap = ap . return

instance Alternative Parser where
  empty = Parser $ \ _ _ -> []
  Parser f <|> Parser g = Parser $ \ xz s ->
    f xz s ++ g xz s

pbind :: String -> Parser a -> Parser a
pbind x (Parser p) = Parser $ \ xz s -> p (xz :< x) s

pscope :: Parser (Bwd String)
pscope = Parser $ \ xz s -> [(xz, s)]

plen :: Parser Int
plen = length <$> pscope

plocal :: Bwd String -> Parser x -> Parser x
plocal xz (Parser p) = Parser $ \ _ s -> p xz s

ppop :: String -> Parser x -> Parser x
ppop x p = pscope >>= \case
  xz :< y | x == y -> plocal xz p
  _ -> empty

pseek :: (String, Int) -> Parser (Either String Int)
pseek (x, n) = Parser $ \ xz s -> let
  chug B0 n = [Left x]
  chug (xz :< y) n
    | y == x = if n == 0 then [Right 0] else fmap (1+) <$> chug xz (n - 1)
    | otherwise = fmap (1+) <$> chug xz n
  in (, s) <$> chug xz n

pch :: (Char -> Bool) -> Parser Char
pch p = Parser $ \ xz s -> case s of
  c : cs | p c -> [(c, cs)]
  _ -> []

pend :: Parser ()
pend = Parser $ \ xz s -> case s of
  [] -> [((), "")]
  _ -> []

parse :: Parser x -> String -> x
parse p s = case parser (id <$> p <* pend) B0 s of
  [(x, _)] -> x
  x -> error (show $ length x)
