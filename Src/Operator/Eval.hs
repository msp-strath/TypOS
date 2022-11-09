{-# LANGUAGE ExistentialQuantification #-}
module Operator.Eval where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Thin
import Term.Base
import Term.Substitution ((//^))
import Concrete.Base
import Operator
import Options
import Actor

dependencySet :: StoreF i d -> Guard -> Set Guard
dependencySet st@Store{..} g = case Map.lookup g guards of
  Nothing -> Set.singleton g
  Just gs -> foldMap (dependencySet st) gs

-- | i stores extra information, typically a naming; d is a date type
data StoreF i d = Store
  { solutions :: Map Meta (i, Maybe Term)
  , guards :: Map Guard (Set Guard) -- key is conjunction of values; acyclic!
  , today :: d
  } deriving (Show, Functor)

data HeadUpData = forall i d. HeadUpData
  { opTable :: Operator -> Clause
  , metaStore :: StoreF i d
  , huOptions :: Options
  , huEnv :: Env
  }

-- Expanding the term using the information currently available:
-- + meta solutions
-- + operator clauses
headUp :: HeadUpData -> Term -> Term
headUp dat@HeadUpData{..} term = case expand term of
  m :$: sg | Just (_, Just t) <- Map.lookup m (solutions metaStore)
    -> headUp dat (t //^ sg)
  t :-: o -> case expand o of
    AX op i -> operate (Operator op) (t, [])
    o@(CdB (A op) th :%: wargs) ->
      case asList (\ ps -> pure $ operate (Operator op) (t, ps)) wargs of
        Nothing -> contract (t :-: contract o)
        Just t -> t
    o -> contract (t :-: contract o)
  GX g t -> if Set.null (dependencySet metaStore g) then headUp dat t else term
  _ -> term

  where

  operate :: Operator -> (Term, [Term]) -> Term
  operate op tps = case runClause (opTable op) huOptions (headUp dat) huEnv tps of
    Left (t, ps) -> t -% (getOperator op, ps)
    Right t -> headUp dat t


