{-# LANGUAGE OverloadedStrings, StandaloneDeriving #-}

module Actor where


import qualified Data.Map as Map

import Bwd
import Display
import Term
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
instance Display PatVar where
  display na@(ns, _, _) = \case
    VarP n -> ns <! n

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

instance Display Env where
  display na (Env sc avs als) =
    collapse $
    map (\ (av, (xs, t)) -> concat (show (ActorVar av) : map (" " ++) xs ++ [" = ", display (foldl nameOn na xs) t])) (Map.toList avs)
    ++ map (\ (al, i) -> show (Alias al) ++ " = " ++ display na (var i sc :: Term)) (Map.toList als)


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

instance Display Actor where
  display na = \case
    a :|: b -> pdisplay na a ++ " :|: " ++ pdisplay na b
    Closure env a -> unwords ["Closure", display na env, pdisplay na a]
    Spawn jd ch a -> unwords ["Spawn", jd, show ch, pdisplay na a]
    Send ch tm a -> unwords ["Send", show ch, pdisplay initNaming tm, pdisplay na a]
    Recv ch av a -> unwords ["Recv", show ch, av, pdisplay na a]
    FreshMeta av a -> unwords ["FreshMeta", av, pdisplay na a]
    Under x a -> unwords ["Under", x, pdisplay na a]
    Match lbl tm pts -> unwords ["Match", lbl, pdisplay initNaming tm, collapse (display na <$> pts)]
    Constrain s t -> unwords ["Constrain", pdisplay initNaming s, pdisplay initNaming t]
    Extend (jd, ml, i, a) b ->
      unwords ["Extend", jd, ml, i, pdisplay na a, pdisplay na b]
    Fail gr -> unwords ["Fail", gr]
    Win -> "Win"
    Break str a -> display na a

instance Display t => Display (PatF t, Actor) where
  display na (p, a) = display na p ++ " -> " ++ display na a


mangleActors :: Env -> CdB (Tm ActorMeta) -> Maybe Term
mangleActors env@(Env sc _ _) tm = go tm
 where
  go :: CdB (Tm ActorMeta) -> Maybe Term
  go tm = case expand tm of
    m :$: sbst -> (//^) <$> noisyLookupVar env m <*> goSbst env sbst
    VX i _ -> pure $ var i sc
    AX s _ -> pure $ atom s sc
    a :%: b -> (%) <$> go a <*> go b
    x :.: t -> (x \\) <$> mangleActors (weakenEnv 1 env) t

  goSbst :: Env -> CdB (Sbst ActorMeta) -> Maybe Subst
  goSbst env' (S0 :^^ 0, _)
    = pure (S0 :^^ sc, ones sc <> none (scopeEnv env' - sc))
  goSbst env (ST rp :^^ 0, th) = splirp (rp, th) $ \s (x := tm, ph) -> do
    s <- goSbst env s
    tm <- mangleActors env (tm, ph)
    pure $ sbstT s ((x :=) $^ tm)
  goSbst env (sbst :^^ w, th) = do
    let (ph, ts) = thChop th w
    let env' = strengthenEnv w env
    sbst <- goSbst env' (sbst :^^ 0, ph)
    pure $ sbstW sbst ts

  noisyLookupVar :: Env -> ActorMeta -> Maybe Term
  noisyLookupVar env av = case lookupVar env av of
    Just t -> Just t
    Nothing -> alarm ("couldn't find " ++ show av ++ " in " ++ show env) Nothing

  lookupVar :: Env -> ActorMeta -> Maybe Term
  lookupVar (Env sc avs als) = \case
    ActorVar av -> snd <$> Map.lookup av avs
    Alias al    -> var <$> Map.lookup al als <*> pure sc
