{-# LANGUAGE DeriveFunctor, FlexibleInstances, OverloadedStrings, StandaloneDeriving #-}

module Actor where

import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.String (IsString(..))

import Bwd
import Display
import Hide
import Term
import Thin
import ANSI

import Debug.Trace

dmesg = trace

-- TODO:
--  A zipper for process trees

type Store = Map.Map Meta Term
-- | Stands for a term

type Alias = String
type ActorVar = String
data ActorMeta
  = Alias Alias     -- actor variable standing for a term variable
  | ActorVar ActorVar
  deriving (Eq, Ord)

data PatVar = AliasP Alias | VarP Int
  deriving (Show)
instance Display PatVar where
  display na@(ns, _, _) = \case
    AliasP al -> al
    VarP n -> ns <! n

instance IsString ActorMeta where fromString = ActorVar
instance Show ActorMeta where
  show (Alias str)    = 'v' : str
  show (ActorVar str) = '^' : str

data Channel = Channel String deriving (Eq)
instance Show Channel  where show (Channel str)  = str
instance IsString Channel  where fromString = Channel

type MatchLabel = String
type JudgementForm = String
type Gripe = String

data Env = Env
  { scopeEnv  :: Int
  , actorVars :: Map.Map String ([String], Term)
  , aliases   :: Map.Map String Int -- names to de Bruijn indices
  } deriving (Show)

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
 deriving (Show)

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

instance Display t => Display (PatF t, Actor) where
  display na (p, a) = display na p ++ " -> " ++ display na a

check :: (JudgementForm, (Channel, Actor))
check = ("check", ("p", Recv "p" "ty" $
                        Recv "p" "tm" $
                        Match "" ("tm" $: sbst0 0)
        [ ("Lam" #? [BP (Hide "x") (MP "body" (ones 1))]
          ,FreshMeta "S" $
           FreshMeta "T" $
            let ty = Constrain ("ty" $: sbst0 0) ("Arr" #%+ [("S" $: sbst0 0), ("T" $: sbst0 0)])
                body = Under "x" $
                       Extend ("synth", "subject", "x", Send "p" ("S" $: sbst0 0) Win) $
                       Spawn "check" "q" $
                       Send "q" ("T" $: sbst0 0) $
                       Send "q" ("body" $: (sbstT (sbst0 0) ((Hide "x" :=) $^ (Alias "x" $: sbst0 0)))) Win
            in  ty :|: body)
        , ("Emb" #? [MP "e" (ones 0)]
          ,Spawn "synth" "q" $
           Send "q" ("e" $: sbst0 0) $
           Recv "q" "S" $
           Constrain ("S" $: sbst0 0) ("ty" $: sbst0 0))
        ]))

synth :: (JudgementForm, (Channel, Actor))
synth =
  ("synth", ("p", Recv "p" "tm" $ Match "subject" ("tm" $: sbst0 0)
           [ ("Rad" #? [MP "t" (ones 0), MP "ty" (ones 0)]
             ,(Spawn "check" "q" $ Send "q" ("ty" $: sbst0 0) $ Send "q" ("t" $: sbst0 0) Win)
              :|:
              (Send "p" ("ty" $: sbst0 0) Win))
           , ("App" #? [MP "f" (ones 0), MP "s" (ones 0)]
             ,FreshMeta "S" $
              FreshMeta "T" $
              let fSyn = Spawn "synth" "q" $
                         Send "q" ("f" $: sbst0 0) $
                         Constrain ("ty" $: sbst0 0) ("Arr" #%+ [("S" $: sbst0 0), ("T" $: sbst0 0)])
                  sChk = Spawn "check" "r" $ Send "r" ("S" $: sbst0 0) $ Send "r" ("s" $: sbst0 0) Win
                  result = Send "p" ("T" $: sbst0 0) Win
              in  fSyn :|: sChk :|: result
             )
           ]))

data Hole = Hole deriving Show

data Frame
  = Rules JudgementForm (Channel, Actor)
  | RulePatch JudgementForm MatchLabel Alias Env Actor
  | LeftBranch Hole (Process () [])
  | RightBranch (Process () []) Hole
  | Spawnee (Hole, Channel) (Channel, Process () [])
  | Spawner (Process () [], Channel) (Channel, Hole)
  | Sent Channel Term
  | Binding String
  | UnificationProblem Term Term
  deriving (Show)

instance Display Frame where
  display na = \case
    Rules jd (ch, a) -> jd ++ " |- {}" -- @" ++ show ch ++ " " ++ pdisplay na a
    RulePatch jd ml i env a -> jd ++ " |- +" ++ ml ++ " " ++ show i ++ " -> {}"{- ++ display na env ++ " " ++ pdisplay na a -}
    LeftBranch Hole p -> "<> | " ++ display na p
    RightBranch p Hole -> display na p ++ " | <>"
    Spawnee (Hole, lch) (rch, p) -> "<> @ " ++ show lch ++ " | " ++ show rch ++ " @ " ++ display na p
    Spawner (p, lch) (rch, Hole) -> display na p ++ " @ " ++ show lch ++ " | " ++ show rch ++ " @ <>"
    Sent ch t -> "!" ++ show ch ++ ". " ++ display na t
    Binding x -> withANSI [SetColour Foreground Yellow, SetWeight Bold]
                 $ "\\" ++ x ++ ". "
    UnificationProblem s t -> display na s ++ " ~? " ++ display na t

instance (Traversable t, Collapse t, Display s) => Display (Process s t) where
  display na p = let (fs', store', env', a') = displayProcess' na p in
     concat ["(", collapse fs', " ", store', {-" ", env',-} " ", a', ")"]

displayProcess' :: (Traversable t, Collapse t, Display s) =>
  Naming -> Process s t -> (t String, String, String, String)
displayProcess' na Process{..} =
     let (fs', na') = runState (traverse go stack) na
         store'     = display initNaming store
         env'       = pdisplay na' env
         a'         = pdisplay na' actor
     in (fs', store', env', a')

    where

    go :: Frame -> State Naming String
    go f = do na <- get
              let dis = display na f
              case f of
                Binding x -> put (na `nameOn` x)
                _ -> pure ()
              pure dis

instance Display Store where
  display na = collapse . map go . Map.toList where
    go :: (Meta, Term) -> String
    go (k, t) = "?" ++ show k ++ " := " ++ display (fromScope (scope t)) t

data Process s t
  = Process
  { stack :: t Frame -- Stack frames ahead of or behind us
  , root  :: Root    -- Name supply
  , env   :: Env     -- definitions in scope
  , store :: s       -- Definitions we know for metas (or not)
  , actor :: Actor   -- The thing we are
  }

deriving instance (Show s, Show (t Frame)) => Show (Process s t)

-- Hardwired judgement forms that we know how to do
judgementForms :: [(JudgementForm, (Channel, Actor))]
judgementForms = [synth, check]

initStack :: Bwd Frame
initStack = B0 <>< map (uncurry Rules) judgementForms

processTest :: Process Store Bwd
processTest
  = Process initStack initRoot (initEnv 0) Map.empty $
      Spawn "check" "p" $
      Send "p" ("Arr" #%+ [nat, "Arr" #%+ [bool, nat]]) $
      Send "p" ("Lam" #%+ ["y" \\ ("Lam" #%+ ["x" \\ ("Emb" #%+ [var 1 2])])]) $
      Win
 where
  nat = ("Nat", 0) #% []
  bool = ("Bool", 0) #% []

debug :: (Traversable t, Collapse t, Display s)
      => String -> Process s t -> Bool
debug str p =
  let (fs', store', env', a') = displayProcess' initNaming p
      p' = unlines $ map ("  " ++) [collapse fs', store', env', a']
  in dmesg ("\n" ++ str ++ "\n" ++ p') False

lookupRules :: JudgementForm -> Bwd Frame -> Maybe (Channel, Actor)
lookupRules jd = go 0 Map.empty where

  go :: Int -> -- number of binders we have traversed on the way out
        Map.Map MatchLabel [(PatActor, Actor)] -> -- accumulated patches
        Bwd Frame -> Maybe (Channel, Actor)
  go bd acc B0 = Nothing
  go bd acc (zf :< f) = case f of
    Binding _  -> go (1+bd) acc zf
    RulePatch jd' ml al env a | jd == jd' -> do
      i <- Map.lookup al (aliases env)
      let pat  = VP (VarP (i + bd))
          env' = weakenEnv bd env
          a'   = a
          acc' = Map.insertWith (++) ml [(pat, Closure env' a')] acc
      go bd acc' zf
    Rules jd' (ch, a) | jd == jd' -> Just (ch, patch acc $ {- fmap (weaks bd)-} a)
    _ -> go bd acc zf

  patch :: Map.Map MatchLabel [(PatActor, Actor)] -> Actor -> Actor
  patch ps (Match ml tm pts) =
    let pts' = fmap (fmap (patch ps)) pts in
    Match ml tm (fromMaybe [] (Map.lookup ml ps) ++ pts')
  patch ps (Recv ch av a) = Recv ch av (patch ps a)
  patch ps a = a

-- run an actor
exec :: Process Store Bwd -> Process Store []
--exec (Process zf _ env store a)
--  | dmesg ("\nexec\n  " ++ unlines (map ("  " ++) [show zf, show store, show env, show a])) False
--  = undefined
exec p | debug "exec" p = undefined
exec p@Process { actor = a :|: b, ..} =
  let (lroot, rroot) = splitRoot root ""
      rbranch = Process [] rroot env () b
  in exec (p { stack = stack :< LeftBranch Hole rbranch, root = lroot, actor = a})
exec p@Process { actor = Closure env' a, ..} =
  exec (p { env = env', actor = a })
-- exec p@Process { actor = Spawn jd spawnerCh actor, ..}
--   | Just (spawnedCh, spawnedActor) <- lookup jd judgementForms
--   = let (subRoot, newRoot) = splitRoot root jd
--         spawner = Process [] newRoot gamma () actor
--     in exec (p { stack = stack :< Spawnee (Hole, spawnedCh) (spawnerCh, spawner)
--                , root = subRoot
--                , actor = spawnedActor })
exec p@Process { actor = Spawn jd spawnerCh actor, ..}
  | Just (spawnedCh, spawnedActor) <- lookupRules jd stack
  = let (subRoot, newRoot) = splitRoot root jd
        spawnee = Process [] subRoot (initEnv $ scopeEnv env) () spawnedActor
    in exec (p { stack = stack :< Spawner (spawnee, spawnedCh) (spawnerCh, Hole)
               , root = newRoot
               , actor })
exec p@Process { actor = Send ch tm a, ..}
  | Just term <- mangleActors env tm
  = let (subRoot, newRoot) = splitRoot root ""
    in send ch (tm, term) (p { stack = stack :<+>: [], root = newRoot, actor = a })
exec p@Process { actor = Recv ch x a, ..}
  = recv ch x (p { stack = stack :<+>: [], actor = a })
exec p@Process { actor = m@(Match lbl s ((pat, a):cs)), ..}
  | Just term <- mangleActors env s
  = match env [(B0, pat, term)]
 where

  toDeBruijn :: Bwd String -> PatVar -> Maybe Int
  toDeBruijn zx = \case
    VarP i -> pure i
    AliasP al -> (+ length zx) <$> Map.lookup al (aliases env)

  match :: Env ->
           [(Bwd String -- binders we have gone under
            , PatActor
            , Term)] -> Process Store []
  match env' [] = exec (p { env = env', actor = a })
  match env' ((zx, MP x ph, (t, th)):xs)
    = let g = bigEnd th - bigEnd ph
      in case thicken (ones g <> ph) th of
            Just ps -> let env' = newActorVar x ((ph ?< zx) <>> [], (t, ps)) env in
                       match env' xs
            -- bug: t may not depend on disallowed things until definitions are expanded
            Nothing -> exec (p { actor = Match lbl s cs })
  match env' ((zx, pat, tm):xs) = case (pat, expand (headUp store tm)) of
    (_, (_ :$: _)) -> move (p { stack = stack :<+>: [], actor = m })
    (VP v, VX j _) | Just i <- toDeBruijn zx v
                   , i == j -> match env' xs
    (AP a, AX b _) | a == b -> match env' xs
    (PP p q, s :%: t) -> match env' ((zx,p,s):(zx,q,t):xs)
    (BP (Hide x) p, _ :.: t) -> match env' ((zx :< x,p,t):xs)
    _ -> exec (p { actor = Match lbl s cs })
exec p@Process { actor = FreshMeta av a, ..} =
  let (xm, root') = meta root av
      xt = xm $: sbstI (scopeEnv env)
      env' = newActorVar av ([], xt) env
  in exec (p { env = env', root = root', actor = a })
exec p@Process { actor = Constrain s t, ..}
  | Just s' <- mangleActors env s
  , Just t' <- mangleActors env t
  -- , dmesg "HERE" True
  -- , dmesg (show env) True
  -- , dmesg (show s ++ " ----> " ++ show s') True
  -- , dmesg (show t ++ " ----> " ++ show t') True
  = unify (p { stack = stack :<+>: [UnificationProblem s' t'], actor = Win })
exec p@Process { actor = Under x a, ..}
  = let stack' = stack :< Binding (x ++ show (scopeEnv env))
        env'   = newAlias x env
        actor' = a
    in exec (p { stack = stack', env = env', actor = actor' })
exec p@Process { actor = Extend (jd, ml, i, a) b, ..}
  = let stack' = stack :< RulePatch jd ml i env a in
    exec (p { stack = stack', actor = b })

exec p@Process {..} = move (p { stack = stack :<+>: [] })

mangleActors :: Env -> CdB (Tm ActorMeta) -> Maybe Term
mangleActors env@(Env sc _ _) tm = go tm
 where
  go :: CdB (Tm ActorMeta) -> Maybe Term
  go tm = case expand tm of
    m :$: sbst -> (//^) <$> lookupVar env m <*> goSbst env sbst
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

  lookupVar :: Env -> ActorMeta -> Maybe Term
  lookupVar (Env sc avs als) = \case
    ActorVar av -> snd <$> Map.lookup av avs
    Alias al    -> var <$> Map.lookup al als <*> pure sc

actorVarsMangler :: Int -> Int -> Mangler (Reader (Bwd Frame))
actorVarsMangler xi ga = Mangler
  { mangGlo = xi
  , mangLoc = ga
  , mangV   = pure (V, none xi -? True)
  , mangB   = actorVarsMangler xi (ga + 1)
  , mangM   = error ""
  , mangSelFrom = \ ph -> actorVarsMangler xi (weeEnd ph)
  }

unify :: Process Store Cursor -> Process Store []
-- unify p | dmesg ("\nunify\n  " ++ show p) False = undefined
--unify (Process zf'@(zf :<+>: up@(UnificationProblem s t) : fs) _ _ store a)
--  | dmesg ("\nunify\n  " ++ show t ++ "\n  " ++ show store ++ "\n  " ++ show a) False = undefined
unify p | debug "unify" p = undefined
unify p@Process { stack = zf :<+>: UnificationProblem s t : fs, ..} =
  case (expand (headUp store s), expand (headUp store t)) of
    (s, t) | s == t      -> unify (p { stack = zf :<+>: fs })
    (a :%: b, a' :%: b') -> unify (p { stack = zf :<+>: UnificationProblem a a' : UnificationProblem b b' : fs })
    (x :.: a, x' :.: a') -> unify (p { stack = zf :<+>: UnificationProblem a a' : fs })
    (m :$: sg, _) | Just p <- solveMeta m sg t (p { stack = zf :<+>: fs }) -> unify p
    (_, m :$: sg) | Just p <- solveMeta m sg s (p { stack = zf :<+>: fs }) -> unify p
    (_, _) -> unify (p { stack = zf :< UnificationProblem s t :<+>: fs })
unify p = move p

solveMeta :: Meta   -- The meta (m) we're solving
          -> Subst  -- The substitution (sg) which acts on m
          -> Term   -- The term (t) that must be equal to m :$ sg and depends on ms
          -> Process Store Cursor
          -> Maybe (Process Store Cursor)
solveMeta m (S0 :^^ _, ph) (tm, th) p@Process{..} = do
  ps <- thicken ph th
  -- FIXME: do a deep occurs check here to avoid the bug from match
  return (p { store = Map.insert m (tm, ps) store })
{-
solveMeta ms m sg t (zf :<+>: fs, root, scope, store, a) = case zf of
  zf' :< DeclMeta m' mt -> case (m == m', mt) of
         (b, Right solution) -> let
           sm = stanMangler 0 scope (Map.singleton m' solution)
           (sg', _) = runWriter $ mangleCdB sm sg
           (t', _) = runWriter $ mangleCdB sm t
          in
            if b then
              unify (zf' <>< map (\ m -> DeclMeta m Nothing) ms :<+>: UnificationProblem t' (solution //^ sg') : DeclMeta m' mt : fs, root, scope, a)
            else
              solveMeta ms m sg' t' (zf' :<+>: DeclMeta m' mt : fs, root, scope, a)
         (True, Left th) -> let
           dm = depMangler [m']
           in
           -- the domain of th and sg should be the same
            if getAny (getConst (mangleCdB dm t *> mangleCdB dm sg)) then
              (zf' <>> map (\ m -> DeclMeta m Nothing) ms ++ DeclMeta m' mt : fs, root, scope, Fail "Occurs check fail")
            else
              _ -- STILL LEFT TO DO
         (False, Left th) -> let
           dm = depMangler [m']
           in
            if getAny (getConst (mangleCdB dm t *> mangleCdB dm sg)) then
              solveMeta (m':ms) m sg t (zf' :<+>: fs, root, scope, a)
            else
              solveMeta ms m sg t (zf' :<+>: DeclMeta m' Nothing : fs, root, scope, a)
  B0 -> (map (\ m -> DeclMeta m Nothing) ms ++ fs, root, scope, Fail "Missing meta") -- should not happen
-}

send :: Channel -> (CdB (Tm ActorMeta), Term) -> Process Store Cursor -> Process Store []
--send ch (tm, term) (Process zfs@(zf :<+>: fs) _ _ _ a)
--  | dmesg ("\nsend " ++ show ch ++ " " ++ show term ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
--send ch (tm, term) p
--  | dmesg ("send "  ++ unlines [show ch, "  " ++ show tm, "  " ++ show term]) False
--  = undefined
--send ch (tm, term) p
--  | dmesg ("send "  ++ show ch ++ " " ++ display (frnaming (stack p)) term) False
--  = undefined
--send ch (tm, term) p
--  | debug ("send "  ++ show ch ++ " " ++ display (frnaming (stack p)) term) p
--  = undefined

send ch (tm, term) (p@Process { stack = B0 :<+>: fs, ..})
  = move (p { stack = B0 <>< fs :<+>: [], actor = Send ch tm actor })
send ch (tm, term) (p@Process { stack = zf :< Spawner (childP, q) (r, Hole) :<+>: fs, ..})
  | r == ch =
  let parentP = p { stack = fs, store = () }
      stack' = zf :< Spawnee (Hole, q) (r, parentP) :< Sent q term <>< stack childP
  in exec (childP { stack = stack', store })
send ch (tm, term) p@Process { stack = zf'@(zf :< Spawnee (Hole, q) (r, parentP)) :<+>: fs, ..}
  | ch == q = exec (p { stack = zf :< Spawnee (Hole, q) (r, parentP { stack = Sent r term : stack parentP }) <>< fs })
  | otherwise = move (p { stack = zf' <>< fs :<+>: [], actor = Send ch tm actor })
send ch (tm, term) p@Process { stack = (zf :< f) :<+>: fs }
  = send ch (tm, term) (p { stack = zf :<+>: (f:fs) })

recv :: Channel -> ActorVar -> Process Store Cursor -> Process Store []
recv ch v p | debug ("recv " ++ show ch ++ " " ++ show v) p = undefined
-- recv ch v (zfs, _, _, _, a)
 -- | dmesg ("\nrecv " ++ show ch ++ " " ++ show v ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
recv ch x p@Process { stack = B0 :<+>: fs, ..}
  = move (p { stack = B0 <>< fs :<+>: [], actor = Recv ch x actor })
recv ch x p@Process { stack = zf :< Sent q y :<+>: fs, ..}
  | ch == q
  = let env' = newActorVar x ([], y) env in
    exec (p { stack = zf <>< fs, env = env' })
recv ch x p@Process { stack = zf'@(zf :< Spawnee (Hole, q) (r, parentP)) :<+>: fs, ..}
  = move (p { stack = zf' <>< fs :<+>: [], actor = Recv ch x actor })
recv ch x p@Process { stack = zf :< f :<+>: fs }
  = recv ch x (p { stack = zf :<+>: (f:fs) })

-- find the next thing to run
move :: Process Store Cursor -> Process Store []
-- move (Process zfs _ _ store a)
-- | dmesg ("\nmove\n  " ++ show zfs ++ "\n  " ++ show store ++ "\n  " ++ show a) False = undefined
-- move p | debug "move" p = undefined

move p@Process { stack = B0 :<+>: fs } = p { stack = fs }
move p@Process { stack = zf :< LeftBranch Hole rp :<+>: fs, ..}
  = exec (rp { stack = zf :< RightBranch (p { stack = fs, store = () }) Hole <>< stack rp, store })
move p@Process { stack = zf :< Spawnee (Hole, q) (r, parentP) :<+>: fs, ..}
  = let childP = p { stack = fs, store = () }
        stack' = zf :< Spawner (childP, q) (r, Hole) <>< stack parentP
    in exec (parentP { stack = stack', store })
move p@Process { stack = (zf :< f) :<+>: fs }
  = move (p { stack = zf :<+>: (f : fs) })

frnaming :: Foldable t => t Frame -> Naming
frnaming zf = (zv, ones (length zv), zv)
 where
  zv = flip foldMap zf $ \case
    Binding x -> B0 :< x
    _ -> B0

headUp :: Store -> Term -> Term
headUp store term
  | m :$: sg <- expand term, Just t <- Map.lookup m store = headUp store (t //^ sg)
  | otherwise = term
