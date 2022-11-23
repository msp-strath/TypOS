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
    ppunc "."
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
  <|> Sbst unknown <$ pch (== '{') <* pspc <*> ppes (ppunc ",") psbstC <* ppunc "}" <*> pTM

  where

  more :: Raw -> Parser Raw
  more t = withRange $
    ((Op unknown t <$ ppunc "-" <*> ptm) >>= more)
    <|> pure t

ptm :: Parser Raw
ptm = withRange $
  Var unknown <$> pvariable
  <|> At unknown <$> patom
  <|> plisp Nothing
  -- <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> pparens pTM

psbstC :: Parser SbstC
psbstC = withRange $ pvariable >>= \ x ->
  Assign unknown x <$ ppunc "=" <*> pTM
  <|> Drop unknown x <$ pspc <* pch (== '*')
  <|> pure (Keep unknown x)

instance Lisp RawP where
  mkNil = AtP unknown ""
  mkCons = ConsP unknown
  pCar = ppat

ppat :: Parser RawP
ppat = withRange $
  AsP unknown <$> pvariable <* ppunc "@" <*> ppat
  <|> VarP unknown <$> pvariable
  <|> AtP unknown <$> patom
  <|> plisp (Just $ pmustwork "Expected a list pattern")
  -- <|> id <$ pch (== '[') <* pspc <*> pmustwork "Expected a list pattern" plisp
  <|> pparens ppat
  <|> pscoped LamP pbinder ppat
  <|> ThP unknown <$ pch (== '{') <* pspc <*> pth <* ppunc "}" <*> ppat
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
psyntaxdecl = pTM

pcontextstack :: Parser (ContextStack Raw)
pcontextstack = ContextStack
  <$> psyntaxdecl
  <* ppunc "->"
  <*> pmustwork "Expected a syntax declaration" psyntaxdecl

pACT :: Parser CActor
pACT = withRange (pact >>= more) where

  more :: CActor -> Parser CActor
  more act = Branch unknown act <$ ppunc "|" <*> pmustwork "Expected an actor" pACT
    <|> pure act

withVar :: Parser x -> String -> Parser a -> Parser (x, a)
withVar px str p = (,) <$> px <* ppunc str <*> p

withVars :: (Range -> (x, a) -> a) -> Parser x -> String -> Parser a -> Parser a
withVars con px str pa = do
  WithRange r (xs, a) <- withRange $ WithRange unknown <$> do
    xs <- psep1 pspc px
    ppunc str
    a <- pa
    pure (xs, a)
  pure $ foldr (curry (con r)) a xs

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
  <|> (isProper =<< plisp Nothing) where
  -- id <$ pch (== '[') <* pspc <*> plisp) where

    isProper :: CScrutinee -> Parser CScrutinee
    isProper (Term _ _) = pfail
    isProper c = pure c

pact :: Parser CActor
pact = withRange $
  pscoped Under pvariable pact
  <|> Send unknown <$> pvariable <*> pure () <* ppunc "!" <*> pmustwork "Expected a term" pTM <* ppunc "." <*> pact
  <|> do tm <- pTM
         ppunc "?"
         case tm of
           Var _ c -> withVars (`Recv` c) ppat "." pact
           t -> withVars (`FreshMeta` t) pvariable "." pact
  <|> Let unknown <$ pkeyword KwLet <* pspc1 <*> pvariable <* ppunc ":" <*> psyntaxdecl
                  <* ppunc "=" <*> pTM <* ppunc "." <*> pact
  <|> Spawn unknown <$> pextractmode <*> pvariable <* ppunc "@" <*> pvariable <* ppunc "." <*> pact
  <|> Constrain unknown <$> pTM <* ppunc "~" <*> pmustwork "Expected a term" pTM
  <|> Connect unknown <$> (CConnect <$> pvariable <* ppunc "<->" <*> pvariable)
  <|> Match unknown <$> pcase <* ppunc "{"
       <*> psep (ppunc ";") ((,) <$> ppat <* ppunc "->" <*> pACT)
       <* pspc <* pch (== '}')
  <|> pparens pACT
  <|> Break unknown <$ pkeyword KwBREAK <* pspc1 <*> (pformat >>= pargs) <* ppunc "." <*> pact
  <|> Print unknown <$ pkeyword KwPRINT <* pspc1 <*> pargs [TermPart Instantiate ()] <* ppunc "." <*> pact
  <|> Print unknown <$ pkeyword KwPRINTF <* pspc1 <*> (pformat >>= pargs) <* ppunc "." <*> pact
  <|> Fail unknown <$ pch (== '#') <* pspc <*> (pformat >>= pargs)
  <|> Push unknown <$> pvariable <* ppunc "|-"
                   <*> ((\ (a, b) -> (a, (), b)) <$> withVar pvariable "->" pTM)
                   <* ppunc "." <*> pact
  <|> Note unknown <$ plit "!" <* ppunc "." <*> pact
  <|> pure (Win unknown)
  where
    -- allows `case$ x` to stand for `case $ x`
    pcase :: Parser CScrutinee
    pcase = pkeyword KwCase <* pspc1 *> pscrutinee
        <|> SubjectVar unknown <$ pkeyword KwCase <* pch ('$' ==) <* pspc1 <*> pvariable

pargs :: [Format dir dbg ()] -> Parser [Format dir dbg Raw]
pargs = traverse $ traverse (\ () -> id <$ pspc <*> pmustwork "Expected a term" pTM)
