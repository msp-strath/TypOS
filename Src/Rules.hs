{-# LANGUAGE UndecidableInstances #-}
module Rules where

import Control.Applicative

import Data.These

import Actor
import Scope
import Concrete.Base
import Machine.Base (DEFNOP, pdefnop)
import Term.Base

import Parse
import Location
import Concrete.Parse

type family FORMULA (ph :: Phase) :: *
type instance FORMULA Concrete = CFormula
type instance FORMULA Abstract = AFormula

data CFormula
  = CFormula (These RawP Raw) -- we don't know if we need a pattern or term yet
  | CCitizen RawP Raw  -- pat => term
  deriving (Show)

data AFormula
  = Coming Pat
  | Going  Term
  | Citizen Pat Term -- pat => term
  deriving (Show)

-- _=>_ should be a constructor of FORMULA?
-- a raw formula is an expression (and we might make it into a pattern later)
data JUDGEMENT (ph :: Phase)
  = Judgement (JUDGEMENTFORM ph) [FORMULA ph]

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

deriving instance
  ( Show (JUDGEMENTFORM ph)
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

pformula :: Parser CFormula
pformula = pcitizen
         <|> CFormula <$> pthese ppat ptm
  where
    pcitizen = pparens pcitizen
             <|> CCitizen <$> ppat <* punc "=>" <*> ptm

pjudgement :: Parser (JUDGEMENT Concrete)
pjudgement = Judgement <$> pvariable <*> many (id <$ pspc <*> pformula)

ppremise :: Parser (PREMISE Concrete)
ppremise = pscoped Binding pbinder ppremise
        <|> (pjudgement >>=
               \ j -> ((Hypothetical j <$ punc "|-" <*> ppremise) <|> (pure $ Premise j)))
        <|> Constraint <$> ptm <* punc "=" <*> ptm

prule :: Parser (RULE Concrete)
prule = RULE <$ pkeyword KwRule <* pspc <*> pcurlies (psep (punc ";") ppremise)
      <* pspc <*> pjudgement <* pspc <*> pcurlies (psep (punc ";") pdefnop)  