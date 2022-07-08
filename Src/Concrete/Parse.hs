module Concrete.Parse where

import Control.Applicative
import Control.Monad

import Bwd
import Concrete.Base
import Format
import Hide
import Parse
import Scope
import Location

instance Lisp Raw where
  mkNil = At unknown ""
  mkCons = Cons unknown
  pCar = ptm

pscoped :: (Range -> Scope x a -> a) ->
           Parser x -> Parser a -> Parser a
pscoped con px pa = do
  WithRange r (xs, a) <- withRange $ WithRange unknown <$> do
    pch (== '\\')
    pspc
    xs <- pmustwork "Expected at least a binder" $
          psep1 pspc (Hide <$> px)
    punc "."
    a <- pa
    pure (xs, a)
  pure $ foldr (\ x a -> con r (Scope x a)) a xs

pkeyword :: Keyword -> Parser ()
pkeyword = plit . show

pvariable :: Parser Variable
pvariable = do
  v <- withRange (Variable unknown <$> pnom)
  let candidate = getVariable v
  let keywords = show <$> [minBound :: Keyword .. maxBound]
  if candidate `elem` keywords
    then Other ("'" ++ candidate ++ "' is a reserved keyword") <!> pfail
    else pure v

pbinder :: Parser (Binder Variable)
pbinder = Used <$> pvariable
      <|> Unused <$ plit "_"

ptm :: Parser Raw
ptm = withRange $
  Var unknown <$> pvariable
  <|> At unknown <$> patom
  <|> pscoped Lam pbinder ptm
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> pparens ptm
  <|> Sbst unknown <$ pch (== '{') <* pspc <*> ppes (punc ",") psbstC <* punc "}" <*> ptm

psbstC :: Parser SbstC
psbstC = withRange $ pvariable >>= \ x ->
  Assign unknown x <$ punc "=" <*> ptm
  <|> Drop unknown x <$ pspc <* pch (== '*')
  <|> pure (Keep unknown x)

instance Lisp RawP where
  mkNil = AtP unknown ""
  mkCons = ConsP unknown
  pCar = ppat

ppat :: Parser RawP
ppat = withRange $
  AsP unknown <$> pvariable <* punc "@" <*> ppat
  <|> VarP unknown <$> pvariable
  <|> AtP unknown <$> patom
  <|> id <$ pch (== '[') <* pspc <*> pmustwork "Expected a list pattern" plisp
  <|> pparens ppat
  <|> pscoped LamP pbinder ppat
  <|> ThP unknown <$ pch (== '{') <* pspc <*> pth <* punc "}" <*> ppat
  <|> UnderscoreP unknown <$ pch (== '_')

pth :: Parser (Bwd Variable, ThDirective)
pth = (,) <$> ppes pspc pvariable
          <*> (ThDrop <$ pspc <* pch ('*' ==) <|> pure ThKeep)

pmode :: Parser Mode
pmode = Input <$ pch (== '?')
    <|> Subject <$ pch (== '$')
    <|> Output <$ pch (== '!')

pprotocol :: Parser (Protocol Raw)
pprotocol = psep pspc
  ((,) <$> pmode <* pspc
       <*> pmustwork "Expected a syntax declaration" psyntaxdecl
       <* pspc <* plit ".")

psyntaxdecl :: Parser Raw
psyntaxdecl = ptm

pcontextstack :: Parser (ContextStack Raw)
pcontextstack = ContextStack
  <$> psyntaxdecl
  <* punc "->"
  <*> pmustwork "Expected a syntax declaration" psyntaxdecl

pACT :: Parser CActor
pACT = withRange (pact >>= more) where

  more :: CActor -> Parser CActor
  more act = Branch unknown act <$ punc "|" <*> pmustwork "Expected an actor" pACT
    <|> pure act

withVar :: Parser x -> String -> Parser a -> Parser (x, a)
withVar px str p = (,) <$> px <* punc str <*> p

withVars :: (Range -> (x, a) -> a) -> Parser x -> String -> Parser a -> Parser a
withVars con px str pa = do
  WithRange r (xs, a) <- withRange $ WithRange unknown <$> do
    xs <- psep1 pspc px
    punc str
    a <- pa
    pure (xs, a)
  pure $ foldr (curry (con r)) a xs

pextractmode :: Parser ExtractMode
pextractmode
    = TopLevelExtract <$ pch (== '/') <* pspc
  <|> InterestingExtract <$ pch (== '^') <* pspc
  <|> pure AlwaysExtract

instance Lisp CScrutinee where
  mkNil = Term unknown mkNil
  mkCons = Pair unknown
  pCar = pscrutinee

pscrutinee :: Parser CScrutinee
pscrutinee = withRange $ do
  Term unknown <$> ptm
  <|> Lookup unknown <$ pkeyword KwLookup <* pspc <*> pvariable <* pspc <*> ptm
  <|> Compare unknown <$ pkeyword KwCompare <* pspc <*> ptm <* pspc <*> ptm
  <|> pparens pscrutinee
  <|> (do sc <- id <$ pch (== '[') <* pspc <*> plisp
          sc <$ unless (isProper sc) pfail)

pact :: Parser CActor
pact = withRange $
  pscoped Under pvariable pact
  <|> Send unknown <$> pvariable <* punc "!" <*> pmustwork "Expected a term" ptm <* punc "." <*> pact
  <|> do tm <- ptm
         punc "?"
         case tm of
           Var _ c -> withVars (`Recv` c) ppat "." pact
           t -> withVars (`FreshMeta` t) pvariable "." pact
  <|> Let unknown <$ pkeyword KwLet <* pspc <*> pvariable <* punc ":" <*> psyntaxdecl
                  <* punc "=" <*> ptm <* punc "." <*> pact
  <|> Spawn unknown <$> pextractmode <*> pvariable <* punc "@" <*> pvariable <* punc "." <*> pact
  <|> Constrain unknown <$> ptm <* punc "~" <*> pmustwork "Expected a term" ptm
  <|> Connect unknown <$> (CConnect <$> pvariable <* punc "<->" <*> pvariable)
  <|> Match unknown <$ pkeyword KwCase <* pspc <*> pscrutinee <* punc "{"
       <*> psep (punc ";") ((,) <$> ppat <* punc "->" <*> pACT)
       <* pspc <* pch (== '}')
  <|> pparens pACT
  <|> Break unknown <$ pkeyword KwBREAK <* pspc <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Print unknown <$ pkeyword KwPRINT <*> pargs [TermPart Instantiate ()] <* punc "." <*> pact
  <|> Print unknown <$ pkeyword KwPRINTF <* pspc <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Fail unknown <$ pch (== '#') <* pspc <*> (pformat >>= pargs)
  <|> Push unknown <$> pvariable <* punc "|-"
                   <*> ((\ (a, b) -> (a, (), b)) <$> withVar pvariable "->" ptm)
                   <* punc "." <*> pact
  <|> Note unknown <$ plit "!" <* punc "." <*> pact
  <|> pure (Win unknown)

pargs :: [Format dir dbg ()] -> Parser [Format dir dbg Raw]
pargs = traverse $ traverse (\ () -> id <$ pspc <*> pmustwork "Expected a term" ptm)
