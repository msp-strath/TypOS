{-# LANGUAGE OverloadedStrings, StandaloneDeriving #-}

module Actor where

import qualified Data.Map as Map

import Hide
import Bwd
import Term
import Pattern
import Thin
import ANSI

type Alias = String
type ActorVar = String
data ActorMeta
  = Alias Alias     -- actor variable standing for a term variable
  | ActorVar ActorVar -- stands for a term
  deriving (Eq, Ord)

data PatVar = VarP Int
  deriving (Show, Eq)

instance Show ActorMeta where
  show (Alias str)    = 'v' : str
  show (ActorVar str) = '^' : str

data Channel = Channel String deriving (Eq)
instance Show Channel  where show (Channel str)  = str

type MatchLabel = String
type JudgementForm = String
type Gripe = String

data Env = Env
  { scopeEnv  :: Int
  , actorVars :: Map.Map String ([String], Term)
  , aliases   :: Map.Map String Int -- names to de Bruijn indices
  } deriving (Show, Eq)

initEnv :: Int -> Env
initEnv gamma = Env gamma Map.empty Map.empty

newAlias :: String -> Env -> Env
newAlias x env =
  let (Env sc avs als) = weakenEnv 1 env in
  Env sc avs (Map.insert x 0 als)

newActorVar :: String -> ([String], Term) -> Env -> Env
newActorVar x defn env@(Env _ avs _) = env { actorVars = Map.insert x defn avs }

weakenEnv :: Int -> Env -> Env
weakenEnv i (Env sc avs als) = Env (sc + i) avs' als' where

  avs' = fmap weakenDefn avs
  als' = fmap (+i) als

  weakenDefn :: ([String], Term) -> ([String], Term)
  weakenDefn (xs, (t, th)) =
    -- 11111 gamma ++ xs 11111        11111 gamma ++ [1..i] : xs 11111
    --         th                -->         ....
    -- 00110 support     00010        00110 support' 0 ... 0  00010
    let n = length xs
        (thl, thr) = thChop th n
    in (xs, (t, thl <> none i <> thr))

strengthenEnv :: Int -> Env -> Env
strengthenEnv 0 env = env
strengthenEnv i (Env sc avs als) = Env (sc - i) avs' als' where

  avs' = fmap strengthenDefn avs
  als' = fmap (\ v -> v - i) als

  strengthenDefn :: ([String], Term) -> ([String], Term)
  strengthenDefn (xs, (t, th)) =
    let n = length xs
        (thl, thr) = thChop th n
    in (xs, (t, fst (thChop thl i) <> thr))

type PatActor = PatF PatVar

infixr 3 :|:
-- We expect all the terms to be closed
data Actor
 = Actor :|: Actor
 | Closure Env Actor
 | Spawn JudgementForm Channel Actor
 | Send Channel (CdB (Tm ActorMeta)) Actor
 | Recv Channel ActorVar Actor
 | FreshMeta ActorVar Actor
 | Under Alias Actor
 | Match MatchLabel (CdB (Tm ActorMeta)) [(PatActor, Actor)]
 -- This is going to bite us when it comes to dependent types
 | Constrain (CdB (Tm ActorMeta)) (CdB (Tm ActorMeta))
 | Extend (JudgementForm, MatchLabel, Alias, Actor) Actor
 | Fail Gripe
 | Win
 | Break String Actor
 deriving (Show, Eq)

mangleActors :: Env -> CdB (Tm ActorMeta) -> Maybe Term
mangleActors env@(Env sc _ _) tm = go tm
 where
  go :: CdB (Tm ActorMeta) -> Maybe Term
  go tm = case expand tm of
    m :$: sbst -> do
      (xs, t) <- noisyLookupVar env m
      sg <- goSbst env (B0 <>< xs) sbst
      pure (t //^ sg)
    VX i _ -> pure $ var i sc
    AX s _ -> pure $ atom s sc
    a :%: b -> (%) <$> go a <*> go b
    x :.: t -> (x \\) <$> mangleActors (weakenEnv 1 env) t

  -- `covers nz x` ensures that `x` is at the most local end of `nz`.
  covers :: Bwd String -> Hide String -> Maybe (Bwd String)
  covers (nz :< n) (Hide x)
    | n == x = pure nz
    | otherwise = let msg = "Subst mismatch: expected " ++ n ++ " got " ++ x in
                  alarm msg (pure nz)
  covers nz _ = pure nz

  goSbst :: Env -> Bwd String -> CdB (Sbst ActorMeta) -> Maybe Subst
--  goSbst env _ (S0 :^^ 0, _) | (scopeEnv env - sc) < 0 = error $ "Oops...! " ++ show (scopeEnv env) ++ " " ++ show sc
  goSbst env _ (S0 :^^ 0, _)
    = pure (S0 :^^ sc, ones sc <> none (scopeEnv env - sc))
  goSbst env nz (ST rp :^^ 0, th) =
    splirp (rp, th) $ \ s (x := tm, ph) -> do
      nz <- nz `covers` x
      s <- goSbst env nz s
      tm <- mangleActors env (tm, ph)
      pure $ sbstT s ((x :=) $^ tm)
  goSbst env nz (sbst :^^ w, th) = do
    let (ph, ts) = thChop th w
    let env' = strengthenEnv w env
    sbst <- goSbst env' nz (sbst :^^ 0, ph)
    pure $ sbstW sbst ts

  noisyLookupVar :: Env -> ActorMeta -> Maybe ([String], Term)
  noisyLookupVar env av = case lookupVar env av of
    Just xst -> Just xst
    Nothing -> alarm ("couldn't find " ++ show av ++ " in " ++ show env) Nothing

  -- Return the term associated to an actor var, together with the
  -- local scope extension it was bound in. We expect that the
  -- substitution acting upon the term will cover all of these local
  -- variables.
  lookupVar :: Env -> ActorMeta -> Maybe ([String], Term)
  lookupVar (Env sc avs als) = \case
    ActorVar av -> Map.lookup av avs
    Alias al    -> ([],) <$> (var <$> Map.lookup al als <*> pure sc)
