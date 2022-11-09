{-# LANGUAGE UndecidableInstances #-}
module Operator where

import Control.Applicative

import Concrete.Base
import Concrete.Parse
import Location
import Parse
import Options
import Actor (Env)
import Term.Base

------------------------------------------------------------------------------
-- Operators

data ANOPERATOR (ph :: Phase) = AnOperator
  { opName :: OPERATOR ph
  , objDesc :: SYNTAXDESC ph
  , paramDescs :: [SYNTAXDESC ph]
  , retDesc :: SEMANTICSDESC ph
  }

deriving instance
  ( Show (OPERATOR ph)
  , Show (SYNTAXDESC ph)
  , Show (SEMANTICSDESC ph)
  ) => Show (ANOPERATOR ph)

type CAnOperator = ANOPERATOR Concrete
type AAnOperator = ANOPERATOR Abstract

data Operator = Operator { getOperator :: String }
  deriving (Show, Eq)

type family OPERATOR (ph :: Phase) :: *
type instance OPERATOR Concrete = WithRange String
type instance OPERATOR Abstract = Operator

newtype Clause = Clause { runClause
  :: Options
  -> (Term -> Term) -- head normaliser
  -> Env
  -> (Term, [Term]) -- object & parameters
  -> Either (Term, [Term]) Term }

instance Semigroup Clause where
  (<>) = mappend

instance Monoid Clause where
  mempty = Clause $ \ _ _ _ -> Left
  mappend cl1 cl2 = Clause $ \ opts hd env ops -> case runClause cl2 opts hd env ops of
    Left ops -> runClause cl1 opts hd env ops
    Right t -> Right t

instance Show Clause where
  show _ = "<fun>"

type OPPATTERN ph = (OPERATOR ph, [PATTERN ph])

type family DEFNOP (ph :: Phase) :: *
type instance DEFNOP Concrete = (PATTERN Concrete, [OPPATTERN Concrete], TERM Concrete)
type instance DEFNOP Abstract = (Operator, Clause)

pdefnop :: Parser (DEFNOP Concrete)
pdefnop =  (,,) <$> ppat <*> some (punc "-" *> poperator ppat) <* punc "~>" <*> pTM

type COpPattern = OPPATTERN Concrete
type AOpPattern = OPPATTERN Abstract
type COperator = OPERATOR Concrete
type AOperator = OPERATOR Abstract

poperator :: Parser a -> Parser (WithRange String, [a])
poperator ph =
  (,[]) <$> pwithRange patom
  <|> (,) <$ pch (== '[') <* pspc <*> pwithRange patom <*> many (id <$ pspc <*> ph) <* pspc <* pch (== ']')

panoperator :: String -> Parser CAnOperator
panoperator copula = do
  obj <- psyntaxdecl
  punc "-"
  (opname, params) <- poperator psyntaxdecl
  punc copula
  ret <- psemanticsdecl
  pure (AnOperator opname obj params ret)

