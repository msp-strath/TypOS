{-# LANGUAGE UndecidableInstances #-}
module Rules where

import Control.Applicative

import Data.These

import Actor
import Scope
import Concrete.Base
import Machine.Base (DEFNOP, ANOPERATOR, pdefnop, panoperator)
import Term.Base

import Parse
import Location
import Concrete.Parse

type family FORMULA (ph :: Phase) :: *
type instance FORMULA Concrete = CFormula
type instance FORMULA Abstract = AFormula

data CFormula
  = CFormula (These RawP Raw) -- we don't know if we need a pattern or term yet
  | CCitizen RawP Raw  -- (pat => term)
  deriving (Show)

data AFormula
  = Coming Pat
  | Going  Term
  | Citizen Pat Term -- pat => term
  deriving (Show)

-- _=>_ should be a constructor of FORMULA?
-- a raw formula is an expression (and we might make it into a pattern later)
data JUDGEMENT (ph :: Phase)
  = Judgement Range (JUDGEMENTNAME ph) [FORMULA ph]

instance HasSetRange (JUDGEMENT ph) where
  setRange r (Judgement _ n fms) = Judgement r n fms

data PREMISE (ph :: Phase)
  = Premise (JUDGEMENT ph)
  | Binding Range (Scope (Binder Variable) (PREMISE ph))
  | Hypothetical (JUDGEMENT ph) (PREMISE ph)
  | Constraint (TERM ph) (TERM ph)

data RULE (ph :: Phase) = RULE
  { premises :: [PREMISE ph]
  , conclusion :: JUDGEMENT ph
  , operatorDefs :: [DEFNOP ph]
  }

type SEMANTICSDESC (ph :: Phase) = TERM ph

type PLACE (ph :: Phase) = (Variable, PLACEKIND ph)

data PLACEKIND (ph :: Phase)
  = CitizenPlace
  | SubjectPlace (SYNTAXDESC ph) (Maybe (SEMANTICSDESC ph))

data JUDGEMENTFORM (ph :: Phase) = JudgementForm
  { jrange :: Range
  , jpreconds :: [JUDGEMENT ph]
  , jname :: JUDGEMENTNAME ph
  , jplaces :: [PLACE ph]
  , jpostconds :: [Either (JUDGEMENT ph) (ANOPERATOR ph)]
  }

instance HasSetRange (JUDGEMENTFORM ph) where
  setRange r (JudgementForm _ a b c d) = JudgementForm r a b c d

deriving instance
  ( Show (JUDGEMENTNAME ph)
  , Show (FORMULA ph)) =>
  Show (JUDGEMENT ph)

deriving instance
  ( Show (JUDGEMENT ph)
  , Show (TERM ph)) =>
  Show (PREMISE ph)

deriving instance
  ( Show (PREMISE ph)
  , Show (JUDGEMENT ph)
  , Show (DEFNOP ph)) =>
  Show (RULE ph)

deriving instance
  ( Show (SYNTAXDESC ph)
  , Show (SEMANTICSDESC ph)) =>
  Show (PLACEKIND ph)

deriving instance
  ( Show (JUDGEMENT ph)
  , Show (JUDGEMENTNAME ph)
  , Show (PLACE ph)
  , Show (ANOPERATOR ph)) =>
  Show (JUDGEMENTFORM ph)

pformula :: Parser CFormula
pformula = pcitizen
         <|> CFormula <$> pthese ppat ptm
  where
    pcitizen = pparens pcitizen
             <|> CCitizen <$> ppat <* punc "=>" <*> ptm

pjudgement :: Parser (JUDGEMENT Concrete)
pjudgement = withRange $ Judgement unknown <$> pvariable <*> many (id <$ pspc <*> pformula)

ppremise :: Parser (PREMISE Concrete)
ppremise = pscoped Binding pbinder ppremise
        <|> (pjudgement >>=
               \ j -> ((Hypothetical j <$ punc "|-" <*> ppremise) <|> (pure $ Premise j)))
        <|> Constraint <$> ptm <* punc "=" <*> ptm

prule :: Parser (RULE Concrete)
prule = RULE <$ pkeyword KwRule <* pspc <*> pcurlies (psep (punc ";") ppremise)
      <* pspc <*> pjudgement <* pspc <*> pcurlies (psep (punc ";") pdefnop)

pplace :: Parser (PLACE Concrete)
pplace = (,CitizenPlace) <$> pvariable
       <|> pparens ((,) <$> pvariable <* punc ":" <*> (SubjectPlace <$> psyntaxdecl <*> optional (id <$ punc "=>" <*> pTM)))

pjudgementform :: Parser (JUDGEMENTFORM Concrete)
pjudgementform = withRange $ JudgementForm unknown <$ pkeyword KwJudgementForm <* pspc <*> pcurlies (psep (punc ";") pjudgement)
                <* pspc <*> pvariable
                <* pspc <*> psep pspc pplace
                <* pspc <*> pcurlies (psep (punc ";") (Left <$> pjudgement <|> Right <$> panoperator ":"))
