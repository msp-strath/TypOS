module Concrete.Parse where

import Control.Applicative

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
  pCar = pTM

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

pTM :: Parser Raw
pTM = withRange $
  (ptm >>= more)
  <|> pscoped Lam pbinder pTM
  <|> Sbst unknown <$ pch (== '{') <* pspc <*> ppes (punc ",") passign <* punc "}" <*> pTM

  where

  more :: Raw -> Parser Raw
  more t = withRange $
    ((Op unknown t <$ punc "-" <*> ptm) >>= more)
    <|> pure t

ptm :: Parser Raw
ptm = withRange $
  Var unknown <$> pvariable
  <|> At unknown <$> patom
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> pparens pTM

passign :: Parser Assign
passign = withRange $ pvariable >>= \ x ->
  Assign unknown x <$ punc "=" <*> pTM

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
  <|> Irrefutable unknown <$ pch (== '~') <* pspc <*> ppat

pth :: Parser (Bwd Variable, ThDirective)
pth = (,) <$> ppes pspc pvariable
          <*> (ThDrop <$ pspc <* pch ('*' ==) <|> pure ThKeep)

pmode :: Parser (Mode ())
pmode = Input <$ pch (== '?')
    <|> Subject () <$ pch (== '$')
    <|> Output <$ pch (== '!')

pprotocol :: Parser CProtocol
pprotocol = Protocol <$> psep pspc
  (mkp <$> pmode <* pspc
       <*> pmustwork "Expected a syntax declaration" psyntaxdecl
       <* pspc <* plit ".")
  where
    mkp :: Mode () -> Raw -> PROTOCOLENTRY Concrete
    mkp m s = (s <$ m, s)

psyntaxdecl :: Parser Raw
psyntaxdecl = pTM

psemanticsdecl :: Parser Raw
psemanticsdecl = pTM

pcontextstack :: Parser CContextStack
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

-- Warning: breaks convention and consumes trailing space
pextractmode :: Parser ExtractMode
pextractmode
    = TopLevelExtract <$ pch (== '/') <* pspc
  <|> InterestingExtract <$ pch (== '^') <* pspc
  <|> pure AlwaysExtract

instance Lisp CScrutinee where
  mkNil = Term unknown (At unknown "")
  mkCons (Term rs s) (Term rt t) = let r = rs <> rt in Term r (Cons r s t)
  mkCons s t = Pair (getRange s <> getRange t) s t
  pCar = pscrutinee

pscrutinee :: Parser CScrutinee
pscrutinee = withRange $ do
  SubjectVar unknown <$ pch ('$' ==) <* pspc <*> pvariable
  <|> Lookup unknown <$ pkeyword KwLookup <* pspc1 <*> pvariable <* pspc <*> pvariable
  <|> Compare unknown <$ pkeyword KwCompare <* pspc1 <*> pTM <* pspc <*> pTM
  <|> pparens pscrutinee
  <|> Term unknown <$> pTM
  <|> (isProper =<< id <$ pch (== '[') <* pspc <*> plisp) where

    isProper :: CScrutinee -> Parser CScrutinee
    isProper (Term _ _) = pfail
    isProper c = pure c

pact :: Parser CActor
pact = withRange $
  pscoped Under pvariable pact
  <|> Send unknown <$> pvariable <*> pure () <* punc "!" <*> pmustwork "Expected a term" pTM <* punc "." <*> pact
  <|> do tm <- pTM
         punc "?"
         case tm of
           Var _ c -> withVars (`Recv` c) ppat "." pact
           t -> withVars (`FreshMeta` t) pvariable "." pact
  <|> Let unknown <$ pkeyword KwLet <* pspc1 <*> pvariable <* punc ":" <*> psyntaxdecl
                  <* punc "=" <*> pTM <* punc "." <*> pact
  <|> Spawn unknown <$> pextractmode <*> pvariable <* punc "@" <*> pvariable <* punc "." <*> pact
  <|> Constrain unknown <$> pTM <* punc "~" <*> pmustwork "Expected a term" pTM
  <|> Connect unknown <$> (CConnect <$> pvariable <* punc "<->" <*> pvariable)
  <|> Match unknown <$> pcase <* punc "{"
       <*> psep (punc ";") ((,) <$> ppat <* punc "->" <*> pACT)
       <* pspc <* pch (== '}')
  <|> pparens pACT
  <|> Break unknown <$ pkeyword KwBREAK <* pspc1 <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Print unknown <$ pkeyword KwPRINT <* pspc1 <*> pargs [TermPart Instantiate ()] <* punc "." <*> pact
  <|> Print unknown <$ pkeyword KwPRINTF <* pspc1 <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Fail unknown <$ pch (== '#') <* pspc <*> (pformat >>= pargs)
  <|> Push unknown <$> pvariable <* punc "|-"
                   <*> ((\ (a, b) -> (a, (), b)) <$> withVar pvariable "->" pTM)
                   <* punc "." <*> pact
  <|> Note unknown <$ plit "!" <* punc "." <*> pact
  <|> pure (Win unknown)
  where
    -- allows `case$ x` to stand for `case $ x`
    pcase :: Parser CScrutinee
    pcase = pkeyword KwCase <* pspc1 *> pscrutinee
        <|> SubjectVar unknown <$ pkeyword KwCase <* pch ('$' ==) <* pspc1 <*> pvariable

pargs :: [Format dir dbg ()] -> Parser [Format dir dbg Raw]
pargs = traverse $ traverse (\ () -> id <$ pspc <*> pmustwork "Expected a term" pTM)
