{-# LANGUAGE UndecidableInstances #-}
module Operator where

import Control.Applicative

import Concrete.Base
import Concrete.Parse
import Location
import Parse
import Options
import Actor ( Env', ACTm)
import Term.Base
import Info
import Bwd
import Thin
import Pretty

{-
  1. No subst in parsing phase.
     => parser has no clue about lexical scope
  2. Elaborator keeps separate notions of CdB context
     and lexical scope.                      ^
             ^                               |
     (maps var names to either CdB vars      |
      or raw terms - the latter must be      |
      in scope at def. site)                 |
                                             |     
     (types in scope for the whole context, weakens under binders,
      never strengthens)
  
-}

data ObjVar = ObjVar
  { objVarName :: String
  , objVarDesc :: Info ASemanticsDesc
  } deriving (Show, Eq)

-- TODO : print the info
instance Pretty ObjVar where
  pretty (ObjVar x info) =  pretty x

-- ObjVars is a representation of variable contexts
-- which are in scope for all the types they contain,
-- i.e. they should be weakened on extension, not on
-- lookup.

newtype ObjVars = ObjVars { getObjVars :: Bwd ObjVar }
  deriving (Show, Eq)

instance Pretty ObjVars where
  pretty = collapse . fmap pretty . getObjVars

thinsTo :: ObjVars -> ObjVars -> Maybe Th
thinsTo (ObjVars x) (ObjVars y) = findSub (objVarName <$> x) (objVarName <$> y)

scopeSize :: ObjVars -> Int
scopeSize = length . getObjVars

(<:) :: ObjVars -> ObjVar -> ObjVars
(ObjVars xz) <: x = ObjVars $ xz :< x


-- Second Order Type
-- i.e. the type of a schematic variable; it can itself bind object variables
-- e.g. ['Pi S \x.T]
--    - S has a SOT, binding nothing
--    - T has a SOT, binding x with type S[]
type family SOT (ph :: Phase) :: *
type instance SOT Concrete = Raw
type instance SOT Abstract = ASOT


-- ObjVars are in scope for the ACTm
data ASOT = ObjVars :=> ACTm
  deriving (Show)

infix 2 :=>

------------------------------------------------------------------------------
-- Operators

data ANOPERATOR (ph :: Phase) = AnOperator
  { opName     :: OPERATOR ph
  , objDesc    :: (Maybe (ACTORVAR ph), PATTERN ph)
  , paramsDesc :: [(Maybe (ACTORVAR ph), SOT ph)]
  , retDesc    :: SOT ph
  }

deriving instance
  ( Show (OPERATOR ph)
  , Show (ACTORVAR ph)
  , Show (PATTERN ph)
  , Show (SOT ph)
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
