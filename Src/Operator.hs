{-# LANGUAGE UndecidableInstances, OverloadedStrings #-}
module Operator where

import Control.Applicative
import Data.Foldable

import Concrete.Base
import Concrete.Parse
import Location
import Parse
import Options
import Actor ( Env', ACTm)
import Term.Base
import Bwd
import Hide
import Scope
import Thin
import Pretty
import Concrete.Pretty()
import Unelaboration.Monad (UnelabMeta)

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

data ObjVar' a = ObjVar
  { objVarName :: String
  , objVarDesc :: a
  } deriving (Functor, Foldable, Traversable, Show, Eq)

type ObjVar = ObjVar' ASemanticsDesc

-- TODO : print the sem
instance Pretty (ObjVar' a) where
  pretty (ObjVar x sem) =  pretty x

-- ObjVars is a representation of variable contexts
-- which are in scope for all the types they contain,
-- i.e. they should be weakened on extension, not on
-- lookup.

newtype ObjVars' a = ObjVars { getObjVars :: Bwd (ObjVar' a) }
  deriving (Functor, Foldable, Traversable, Show, Eq)

type ObjVars = ObjVars' ASemanticsDesc

instance Pretty (ObjVars' a) where
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
type instance SOT Concrete = CSOT
type instance SOT Abstract = ASOT

data CSOT = CSOT
  { sotBinders :: [(Raw, Variable)] -- sort1 \ variable1 . sort2\ variable2. ...
  , sotType :: Raw
  }
  deriving (Show)
-- For the example above:
-- S has CSOT [] 'Semantics
-- T has CSOT [(S,x)] 'Semantics

-- TODO: conversion function to telescope
-- ObjVars are in scope for the ACTm
data ASOT = ObjVars :=> ACTm
  deriving (Show)

infix 2 :=>

data Telescopic a = Stop a
                  | Tele ASemanticsDesc (Scope String (Telescopic a))

discharge :: ObjVars -> a -> Telescopic a
discharge (ObjVars oz) a = go oz (ones (length oz)) (Stop a)
  where
    -- Invariant: Thinning th is from scope of acc into the scope of oz
    go B0 th acc = acc
    go (oz :< ObjVar name ty) th acc = let th' = pop th in
      case thickenCdB th' ty of
        Nothing -> error "discharge: invalid context"
        Just ty -> go oz th' (Tele ty (Scope (Hide name) acc))

------------------------------------------------------------------------------
-- Operators

data ANOPERATOR (ph :: Phase) = AnOperator
 {- (p : ['Sig a \x.b]) -} { objDesc    :: (Binder (ACTORVAR ph), PATTERN ph) -- add ([ACTORVar ph], TERM ph)?
 {- -[ 'snd             -} , opName     :: OPERATOR ph
 {-  ]                  -} , paramsDesc :: [(Binder (ACTORVAR ph), SOT ph)]
 {-  : {x = p -'fst} b  -} , retDesc    :: SEMANTICSDESC ph
                           }

deriving instance
  ( Show (OPERATOR ph)
  , Show (SEMANTICSDESC ph)
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
  .  (Show m, UnelabMeta m) => Options
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
type instance DEFNOP Concrete = ((PATTERN Concrete, PATTERN Concrete) -- object and its type
                                , [OPPATTERN Concrete]                -- spine
                                , TERM Concrete)                      -- right hand side
type instance DEFNOP Abstract = (Operator, Clause)

pdefnop :: Parser (DEFNOP Concrete)
pdefnop =  (,,) <$> ((,) <$> ppat <* ppunc ":" <*> ppat)
                <*> some (ppunc "-" *> poperator ppat)
                <*  ppunc "~>"
                <*> pTM

type COpPattern = OPPATTERN Concrete
type AOpPattern = OPPATTERN Abstract
type COperator = OPERATOR Concrete
type AOperator = OPERATOR Abstract

poperator :: Parser a -> Parser (WithRange String, [a])
poperator ph =
  (,[]) <$> pwithRange patom
  <|> (,) <$ pch (== '[') <* pspc <*> pwithRange patom <*> many (id <$ pspc <*> ph) <* pspc <* pch (== ']')

pBinders :: Parser (a, b) -> Parser (a, ([(Raw, Variable)], b))
pBinders p = fmap . (,) <$> many ((,) <$> pTM <* ppunc "\\" <*> pvariable <* pspc <* pch ('.' ==)) <*> p

panoperator :: Parser CAnOperator
panoperator = do
  obj <- pmaybeNamed ppat (withRange $ pure $ UnderscoreP unknown)
  ppunc "-"
  (opname, params) <- poperator $ pBinders (pmaybeNamed psemanticsdecl pfail)
  ppunc ":"
  AnOperator obj opname (fmap (fmap $ uncurry CSOT) params) <$> psemanticsdecl
 where
  pmaybeNamed :: Parser a -- if binder
              -> Parser a -- if no binder
              -> Parser (Binder (ACTORVAR Concrete), a)
  pmaybeNamed p q
    = pparens ((,) <$> pbinder <* ppunc ":" <*> p)
    <|> ((,) . Used <$> pvariable <*> q)

instance Pretty CAnOperator where
  pretty (AnOperator obj (WithRange _ opName) paramsDesc retDesc) =
    hsep [ prettyNamed obj , args, ":", pretty retDesc ]
      where
        args = case paramsDesc of
          [] -> "-'" <> pretty opName
          xs -> hsep (("-['" <> pretty opName):map prettyNamed paramsDesc) <> "]"
        prettyNamed :: (Pretty a, Pretty b) => (Binder a, b) -> Doc Annotations
        prettyNamed (a, b) = parens $ hsep [pretty a, ":", pretty b]

instance Pretty CSOT where
  pretty (CSOT binders typ) = hsep (map prettyBinders binders ++ [pretty typ])
    where
      prettyBinders (sort, x) = fold [pretty sort, "\\", pretty x, "."]

{-
    {- (p : ['Sig a \x.b]) -} { objDesc    :: (Maybe (ACTORVAR ph), PATTERN ph) -- add ([ACTORVar ph], TERM ph)?
 {- -[ 'snd             -} , opName     :: OPERATOR ph
 {-  ]                  -} , paramsDesc :: [(Maybe (ACTORVAR ph), SOT ph)]
 {-  : {x = p -'fst} b  -} , retDesc    :: SEMANTICSDESC ph
                           }
-}
