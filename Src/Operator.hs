{-# LANGUAGE UndecidableInstances #-}
module Operator where

import Control.Applicative

import Concrete.Base
import Concrete.Parse
import Location
import Parse
import Options
import Actor ( Env')
import Term.Base

------------------------------------------------------------------------------
-- Operators

data ANOPERATOR (ph :: Phase) = AnOperator
  { opName     :: OPERATOR ph
  , objDesc    :: (Maybe (ACTORVAR ph), PATTERN ph)
  , paramDescs :: [(Maybe (ACTORVAR ph), SEMANTICSDESC ph)]
  , retDesc    :: SEMANTICSDESC ph
  }

deriving instance
  ( Show (OPERATOR ph)
  , Show (ACTORVAR ph)
  , Show (PATTERN ph)
  , Show (SEMANTICSDESC ph)
  ) => Show (ANOPERATOR ph)

type CAnOperator = ANOPERATOR Concrete
type AAnOperator = ANOPERATOR Abstract

newtype Operator = Operator { getOperator :: String }
  deriving (Show, Eq)

type family OPERATOR (ph :: Phase) :: *
type instance OPERATOR Concrete = WithRange String
type instance OPERATOR Abstract = Operator

newtype Clause = Clause
  { runClause :: forall m
  .  Options
  -> (Term' m -> Term' m) -- head normaliser
  -> Env' m
  -> (Term' m, [Term' m]) -- object & parameters
  -> Either (Term' m, [Term' m]) (Term' m)
  }

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

panoperator :: Parser CAnOperator
panoperator = do
  obj <- pmaybeNamed ppat  
  punc "-"
  (opname, params) <- poperator $ pmaybeNamed psemanticsdecl
  punc ":"
  AnOperator opname obj params <$> psemanticsdecl
 where
  pmaybeNamed :: Parser a -> Parser (Maybe (ACTORVAR Concrete), a)
  pmaybeNamed p = pparens ((,) . Just <$> pvariable <* punc ":" <*> p)
                 <|> (Nothing,) <$> p
