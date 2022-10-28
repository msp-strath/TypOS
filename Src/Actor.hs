module Actor where

import Data.Map (Map)
import qualified Data.Map as Map

import Alarm
import Bwd
import Concrete.Base
import Hide
import Location
import Options
import Pattern
import Syntax (SyntaxDesc)
import Term
import Thin

type ActorVar = String

type Pat = Pat' ActorMeta

data Passport = ASubject | ACitizen
  deriving (Show, Eq, Ord)

data ActorMeta = ActorMeta Passport ActorVar
  deriving (Eq, Ord)

instance Show ActorMeta where
  show (ActorMeta _ str) = str

newtype Stack = Stack { rawStack :: String }
  deriving (Show, Eq)

newtype Channel = Channel { rawChannel :: String }
  deriving (Show, Eq, Ord)

type JudgementName = String
type Gripe = String

type instance JUDGEMENTNAME Abstract = JudgementName
type instance CHANNEL Abstract = Channel
type instance BINDER Abstract = (Binder ActorMeta)
type instance ACTORVAR Abstract = ActorMeta
type instance SYNTAXDESC Abstract = SyntaxDesc
type instance TERMVAR Abstract = DB
type instance TERM Abstract = ACTm
type instance PATTERN Abstract = Pat
type instance CONNECT Abstract = AConnect
type instance STACK Abstract = Stack
type instance STACKDESC Abstract = SyntaxDesc
type instance SCRUTINEEVAR Abstract = ACTm
type instance SCRUTINEETERM Abstract = ACTm
type instance LOOKEDUP Abstract = ACTm
type instance GUARD Abstract = Maybe ActorVar

data AConnect = AConnect Channel Th Channel Int deriving (Show)
type AProtocol = PROTOCOL Abstract
type AContextStack = ContextStack SyntaxDesc
type AActor = ACTOR Abstract
type ACTm = CdB (Tm ActorMeta)
type ACTSbst = CdB (Sbst ActorMeta)
type AScrutinee = SCRUTINEE Abstract


aconnect :: Range -> Channel -> Th -> Channel -> Int -> AActor
aconnect r ch1 th ch2 n
  | n > 0 = Connect r (AConnect ch1 th ch2 n)
  | otherwise = Win r


data Env = Env
  { globalScope :: Bwd String -- free vars ga actor does *not* know about
  , actorVars :: Map ActorMeta ([String] -- bound vars xi actorVar does know about
                                   , Term) -- in scope ga <>< xi
  , subjectGuards :: Map String Guard                
  , localScope :: Bwd String -- vars de actor has bound
  , alphaRenamings :: Map String (Hide String)
  } deriving (Show, Eq)

tryAlpha :: Env -> String -> String
tryAlpha rho x = maybe x unhide (Map.lookup x (alphaRenamings rho))

declareAlpha :: (String, Hide String) -> Env -> Env
declareAlpha (x, Hide "_") rho = rho
declareAlpha ("_", y) rho = rho
declareAlpha (x, y) rho =
  rho { alphaRenamings = Map.insert x y (alphaRenamings rho) }

initEnv :: Bwd String -> Env
initEnv gamma = Env            
  { globalScope = gamma          
  , actorVars = Map.empty        
  , subjectGuards = Map.empty    
  , localScope = B0              
  , alphaRenamings = Map.empty   
  }
  
childEnv :: Env -> Env
childEnv parentEnv = initEnv (globalScope parentEnv <> localScope parentEnv)

newActorVar :: ActorMeta -> ([String], Term) -> Env -> Env
newActorVar x defn env = env { actorVars = Map.insert x defn (actorVars env) }

guardSubject :: ActorVar -> ([String], Term) -> Guard -> Env -> Env
guardSubject v defn gd env =
  env { subjectGuards = Map.insert v gd (subjectGuards env)
      , actorVars = Map.insert (ActorMeta ACitizen v) (interpreted defn) (actorVars env)}
    where
      interpreted (bs, t) = (bs, contract (GX gd t))
      
-- | When we encounter a term with actor variables inside and want to send
--   or match on it, we need to first substitute all of the terms the actor
--   variables map to.
--  e.g. when considering
--       `case tm { ['Lam \x.body] -> ... }`
--       in the environment (tm := ['Lam \x.['Emb x]])
--  we need to instantiate tm to ['Lam \x.['Emb x]] before
-- trying to find the clause that matches
mangleActors :: Options
             -> Env          {- Env ga -}
             -> ACTm         {- Src de -}
             -> Maybe Term   {- Trg (ga <<< de) -}
mangleActors opts rho tm = go tm where
  ga = length (globalScope rho)

  go :: CdB (Tm ActorMeta) {- Src de -}
     -> Maybe Term         {- Trg (ga <<< de) -}
  go tm = case expand tm of
    VX i de -> pure (var i (ga + de))
    AX a de -> pure (atom a (ga + de))
    a :%: b -> (%) <$> go a <*> go b
    t :-: o -> Term.contract <$> ((:-:) <$> go t <*> go o)
    x :.: t -> (tryAlpha rho x \\) <$> go t
    m :$: sg -> do
      t <- noisyLookupVar m
      sg <- goSbst sg
      pure (t //^ sg)

  goSbst :: CdB (Sbst ActorMeta) {-        xi =>Src de -}
         -> Maybe Subst          {- ga <<< xi =>Trg ga <<< de -}
  goSbst (CdB (S0 :^^ 0) th) = pure $ sbstI ga *^ (ones ga <> th)
  goSbst (CdB (ST rp :^^ 0) th) =
    splirp (CdB rp th) $ \ s (CdB (x := tm) ph) -> do
      s <- goSbst s
      tm <- go (CdB tm ph)
      pure (sbstT s ((x :=) $^ tm))
  goSbst (CdB (sg :^^ w) th) = do
    let (thl, thr) = chopTh w th
    sg <- goSbst (CdB (sg :^^ 0) thl)
    pure $ sbstW sg thr

  -- Return the term associated to an actor var, together with the
  -- local scope extension it was bound in. We expect that the
  -- substitution acting upon the term will cover all of these local
  -- variables.
  lookupVar :: Env -> ActorMeta -> Maybe ([String], Term)
  lookupVar rh av = Map.lookup av (actorVars rh)

  noisyLookupVar :: ActorMeta -> Maybe Term
  noisyLookupVar av = case lookupVar rho av of
    Just (_, t) -> Just t
    Nothing -> alarm opts ("couldn't find " ++ show av ++ " in " ++ show rho)
                       Nothing
