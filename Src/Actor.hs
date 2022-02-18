module Actor where

import qualified Data.Map as Map

import ANSI
import Bwd
import Format
import Hide
import Pattern
import Scope
import Term
import Thin

type ActorVar = String

data ActorMeta = ActorMeta ActorVar
  deriving (Eq, Ord)

instance Show ActorMeta where
  show (ActorMeta str) = str

data Channel = Channel String deriving (Eq, Ord)
instance Show Channel  where show (Channel str)  = str

data MatchLabel = MatchLabel (Maybe String)
  deriving (Show, Eq, Ord)

type JudgementForm = String
type Gripe = String

data Env = Env
  { scopeEnv  :: Int
  , actorVars :: Map.Map ActorMeta ([String], Term)
  } deriving (Show, Eq)

initEnv :: Int -> Env
initEnv gamma = Env gamma Map.empty

newActorVar :: ActorMeta -> ([String], Term) -> Env -> Env
newActorVar x defn env@(Env _ avs) = env { actorVars = Map.insert x defn avs }

instance Thable Env where
  Env sc avs *^ th = Env (bigEnd th) (fmap thinDefn avs) where

    thinDefn :: ([String], Term) -> ([String], Term)
    thinDefn (xs, CdB (t, ph)) = (xs, CdB (t, ph <^> (th <> ones (length xs))))

weakenEnv :: Int -> Env -> Env
weakenEnv i rho = rho *^ (ones (scopeEnv rho) <> none i)

type PatActor = PatF PatVar

infixr 3 :|:
data Actor
 = Actor :|: Actor
 | Closure Env Actor
 | Spawn JudgementForm Channel Actor
 | Send Channel (CdB (Tm ActorMeta)) Actor
 | Recv Channel ActorMeta Actor
 | FreshMeta ActorMeta Actor
 | Under (Scope Actor)
 | Match MatchLabel (CdB (Tm ActorMeta)) [(PatActor, Actor)]
 -- This is going to bite us when it comes to dependent types
 | Constrain (CdB (Tm ActorMeta)) (CdB (Tm ActorMeta))
 | Extend (JudgementForm, MatchLabel, PatVar, Actor) Actor
 | Fail Gripe
 | Win
 | Print [Format Directive Debug (CdB (Tm ActorMeta))] Actor
 | Break String Actor
 deriving (Show, Eq)

instance Thable Actor where
  a *^ th = case a of
    a :|: b -> a *^ th :|: b *^ th
    Closure rho a -> Closure (rho *^ th) (a *^ th)
    Spawn jd ch a -> Spawn jd ch (a *^ th)
    Send ch t a -> Send ch (t *^ th) (a *^ th)
    Recv ch av a -> Recv ch av (a *^ th)
    FreshMeta av a -> FreshMeta av (a *^ th)
    Under sc -> Under (sc *^ th)
    Match ml t pas -> Match ml (t *^ th) (map (fmap (*^ th)) pas)
    Constrain s t -> Constrain (s *^ th) (t *^ th)
    Extend (jd, ml, pv, a) b -> Extend (jd, ml, pv *^ th, a *^ th) (b *^ th)
    Fail gr -> Fail gr
    Win -> Win
    Print fmt a -> Print (map (fmap (*^ th)) fmt) (a *^ th)
    Break str a -> Break str (a *^ th)


-- | When we encounter a term with actor variables inside and want to send
--   or match on it, we need to first substitute all of the terms the actor
--   variables map to.
--  e.g. when considering
--       `case tm { ['Lam \x.body] -> ... }`
--       in the environment (tm := ['Lam \x.['Emb x]])
--  we need to instantiate tm to ['Lam \x.['Emb x]] before
-- trying to find the clause that matches
mangleActors :: Env                {- Env ga -}
             -> CdB (Tm ActorMeta) {- Src ga -}
             -> Maybe Term         {- Trg ga -}
mangleActors rho tm = case expand tm of
  VX i ga -> pure (var i ga)
  AX a ga -> pure (atom a ga)
  a :%: b -> (%) <$> mangleActors rho a <*> mangleActors rho b
  x :.: t -> (x \\) <$> mangleActors (weakenEnv 1 rho) t
  m :$: sg -> do
    (xs, t) <- noisyLookupVar m
    let xi = B0 <>< xs
    sg <- goSbst xi sg
    pure (t //^ sg)

  where

    goSbst :: Bwd String {- xi -}
           -> CdB (Sbst ActorMeta) {-        xi =>Src ga -}
           -> Maybe Subst          {- ga <<< xi =>Trg ga -}
    goSbst B0 (CdB (S0 :^^ 0, th)) = pure (sbstI (bigEnd th))
    goSbst nz (CdB (ST rp :^^ 0, th)) =
      splirp (CdB (rp, th)) $ \ s (CdB (x := tm, ph)) -> do
        nz <- nz `covers` x
        s <- goSbst nz s
        tm <- mangleActors rho (CdB (tm, ph))
        pure (sbstT s ((x :=) $^ tm))
    goSbst nz@(_ :< n) (CdB (sg :^^ w, th)) = do
      let x = (Hide n :=) $^ (var 0 (weeEnd th) *^ th)
      goSbst nz (sbstT (CdB (sg :^^ (w-1), pop th)) x)

    -- Return the term associated to an actor var, together with the
    -- local scope extension it was bound in. We expect that the
    -- substitution acting upon the term will cover all of these local
    -- variables.
    lookupVar :: Env -> ActorMeta -> Maybe ([String], Term)
    lookupVar (Env sc avs) av = Map.lookup av avs

    -- `covers nz x` ensures that `x` is at the most local end of `nz`.
    covers :: Bwd String -> Hide String -> Maybe (Bwd String)
    covers (nz :< n) (Hide x)
      | n == x = pure nz
      | otherwise = let msg = "Subst mismatch: expected " ++ n ++ " got " ++ x in
                    alarm msg (pure nz)
    covers nz _ = pure nz

    noisyLookupVar :: ActorMeta -> Maybe ([String], Term)
    noisyLookupVar av = case lookupVar rho av of
      Just xst -> Just xst
      Nothing -> alarm ("couldn't find " ++ show av ++ " in " ++ show rho)
                       Nothing
