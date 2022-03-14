module Actor where

import qualified Data.Map as Map

import ANSI
import Bwd
import Format
import Hide
import Pattern
import Scope
import Syntax (SyntaxCat)
import Term
import Thin

type ActorVar = String

data ActorMeta = ActorMeta ActorVar
  deriving (Eq, Ord)

instance Show ActorMeta where
  show (ActorMeta str) = str

newtype Channel = Channel { rawChannel :: String }
  deriving (Show, Eq, Ord)

type JudgementForm = String
type Gripe = String

data Env = Env
  { globalScope :: Bwd String -- free vars ga actor does *not* know about
  , actorVars :: Map.Map ActorMeta ([String] -- bound vars xi actorVar does know about
                                   , Term) -- in scope ga <>< xi
  , localScope :: Bwd String -- vars de actor has bound
  , alphaRenamings :: Map.Map String (Hide String)
  } deriving (Show, Eq)

tryAlpha :: Env -> String -> String
tryAlpha rho x = maybe x unhide (Map.lookup x (alphaRenamings rho))

declareAlpha :: (String, Hide String) -> Env -> Env
declareAlpha (x, y) rho =
  rho { alphaRenamings = Map.insert x y (alphaRenamings rho) }

initEnv :: Bwd String -> Env
initEnv gamma = Env gamma Map.empty B0 Map.empty

childEnv :: Env -> Env
childEnv parentEnv = initEnv (globalScope parentEnv <> localScope parentEnv)

newActorVar :: ActorMeta -> ([String], Term) -> Env -> Env
newActorVar x defn env = env { actorVars = Map.insert x defn (actorVars env) }

infixr 3 :|:
data Actor
 = Actor :|: Actor
 | Spawn JudgementForm Channel Actor
 | Send Channel (CdB (Tm ActorMeta)) Actor
 | Recv Channel (ActorMeta, Actor)
 | FreshMeta SyntaxCat (ActorMeta, Actor)
 | Under (Scope Actor)
 | Match (CdB (Tm ActorMeta)) [(Pat, Actor)]
 -- This is going to bite us when it comes to dependent types
 | Constrain (CdB (Tm ActorMeta)) (CdB (Tm ActorMeta))
 | Push JudgementForm (DB, CdB (Tm ActorMeta)) Actor
 | Lookup (CdB (Tm ActorMeta)) (ActorMeta, Actor) Actor
 | Win
 | Fail  [Format Directive Debug (CdB (Tm ActorMeta))]
 | Print [Format Directive Debug (CdB (Tm ActorMeta))] Actor
 | Break [Format Directive Debug (CdB (Tm ActorMeta))] Actor
 deriving (Show, Eq)

-- | When we encounter a term with actor variables inside and want to send
--   or match on it, we need to first substitute all of the terms the actor
--   variables map to.
--  e.g. when considering
--       `case tm { ['Lam \x.body] -> ... }`
--       in the environment (tm := ['Lam \x.['Emb x]])
--  we need to instantiate tm to ['Lam \x.['Emb x]] before
-- trying to find the clause that matches
mangleActors :: Env                {- Env ga -}
             -> CdB (Tm ActorMeta) {- Src de -}
             -> Maybe Term         {- Trg (ga <<< de) -}
mangleActors rho tm = go tm where
  ga = length (globalScope rho)

  go :: CdB (Tm ActorMeta) {- Src de -}
     -> Maybe Term         {- Trg (ga <<< de) -}
  go tm = case expand tm of
    VX i de -> pure (var i (ga + de))
    AX a de -> pure (atom a (ga + de))
    a :%: b -> (%) <$> go a <*> go b
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
    Nothing -> alarm ("couldn't find " ++ show av ++ " in " ++ show rho)
                       Nothing
