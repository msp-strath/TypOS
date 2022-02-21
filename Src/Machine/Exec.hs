module Machine.Exec where

import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

import ANSI
import Bwd
import Display
import Hide
import Pattern
import Scope
import Term
import Thin

import Actor
import Machine.Base
import Machine.Display

import System.IO.Unsafe

import Debug.Trace
dmesg = trace

lookupRules :: Th -> JudgementForm -> Bwd Frame -> Maybe (Channel, Actor)
lookupRules th jd = go th Map.empty where

  go :: Th -> -- how to transport the local scope in the stack into the target one
        Map.Map MatchLabel [(PatActor, Actor)] -> -- accumulated patches
        Bwd Frame -> Maybe (Channel, Actor)
  go th acc B0 = Nothing
  go th acc (zf :< f) = case f of
    Binding _  -> go (pop th) acc zf
    RulePatch jd' ml v env a | jd == jd' -> do
      let acc' = Map.insertWith (++) ml [(VP (v *^ th), ((Closure env a) *^ th))] acc
      go th acc' zf
    Rules jd' (ch, a) | jd == jd' -> Just (ch, patch acc (a *^ th))
    _ -> go th acc zf

  patch :: Map.Map MatchLabel [(PatActor, Actor)] -> Actor -> Actor
  patch ps (Match ml tm pts) =
    let pts' = fmap (fmap (patch ps)) pts in
    Match ml tm (fromMaybe [] (Map.lookup ml ps) ++ pts')
  patch ps (Recv ch av a) = Recv ch av (patch ps a)
  patch ps a = a

-- run an actor
exec :: Process Store Bwd -> Process Store []
-- exec (Process zf _ env store a)
--   | dmesg ("\nexec\n  " ++ unlines (map ("  " ++) [show a])) False
--   = undefined
exec p | debug MachineExec "" p = undefined
exec p@Process { actor = a :|: b, ..} =
  let (lroot, rroot) = splitRoot root ""
      rbranch = Process tracing [] rroot env (today store) b
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
  | Just (spawnedCh, spawnedActor) <- lookupRules (ones (scopeEnv env)) jd stack
  , dmesg (show spawnedActor) True
  = let (subRoot, newRoot) = splitRoot root jd
        spawnee = Process tracing [] subRoot (initEnv $ scopeEnv env) (today store) spawnedActor
    in exec (p { stack = stack :< Spawner (spawnee, spawnedCh) (spawnerCh, Hole)
               , root = newRoot
               , actor })
exec p@Process { actor = Send ch tm a, ..}
  | Just term <- mangleActors env tm
  = let (subRoot, newRoot) = splitRoot root ""
    in send ch (tm, term) (p { stack = stack :<+>: [], root = newRoot, actor = a })
exec p@Process { actor = Recv ch x a, ..}
  = recv ch x (p { stack = stack :<+>: [], actor = a })
exec p@Process { actor = m@(Match lbl s cls), ..}
  | Just term <- mangleActors env s
  = switch term cls
 where

  switch :: Term -> [(PatActor, Actor)] -> Process Store []
  switch t [] =
    let na = frnaming stack
        msg = unlines $
                [ "No matching clause for: " ++ display na (instantiate store t)
                , "(raw term: " ++ display na t ++ ")"
                , "in: case" ++ display initNaming lbl ++ " " ++ display na s
                ] ++ zipWith (\ cs cl -> "  " ++ cs ++ display na cl) ("{ ":repeat "; ") cls
                  ++ ["  }"]
    in alarm msg $ move (p { stack = stack :<+>: [] })
  switch t ((pat, a):cs) = case match env [(B0, pat,t)] of
    Left True -> switch t cs
    Left False -> move (p { stack = stack :<+>: [] })
    Right env -> exec (p { env = env, actor = a } )

  match :: Env ->
           [(Bwd String -- binders we have gone under
            , PatActor
            , Term)] -> Either Bool Env -- Bool: should we keep trying other clauses?
  match env [] = pure env
  match env ((zx, MP x ph, CdB (t, th)):xs) = do
    let g = bigEnd th - bigEnd ph
    -- we can do better: t may not depend on disallowed things until definitions are expanded
    ps <- maybe (Left True) Right $ thicken (ones g <> ph) th
    env <- pure $ newActorVar (ActorMeta x) ((ph ?< zx) <>> [], CdB (t, ps)) env
    match env xs
  match env ((zx, pat, tm):xs) = case (pat, expand (headUp store tm)) of
    (_, (_ :$: _)) -> Left False
    (VP (VarP i), VX j _) | i == j -> match env xs
    (AP a, AX b _) | a == b -> match env xs
    (PP p q, s :%: t) -> match env ((zx,p,s):(zx,q,t):xs)
    (BP (Hide x) p, _ :.: t) -> match env ((zx :< x,p,t):xs)
    _ -> Left True

exec p@Process { actor = FreshMeta av@(ActorMeta x) a, ..} =
  let (xm, root') = meta root x
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
  = unify (p { stack = stack :<+>: [UnificationProblem (today store) s' t'], actor = Win })
exec p@Process { actor = Under (Scope (Hide x) a), ..}
  = let stack' = stack :< Binding (x ++ show (scopeEnv env))
        env'   = weakenEnv 1 env
        actor' = a
    in exec (p { stack = stack', env = env', actor = actor' })
exec p@Process { actor = Extend (jd, ml, i, a) b, ..}
  = let stack' = stack :< RulePatch jd ml i env a in
    exec (p { stack = stack', actor = b })

exec p@Process { actor = Print fmt a, ..}
  | Just format <- traverse (traverse $ mangleActors env) fmt
  =  unsafePerformIO $ do
      putStrLn $ withANSI [SetColour Background Magenta]
               $ display (frnaming stack)
               $ insertDebug p
               $ instantiate store format
      _ <- getLine
      pure (exec (p { actor = a }))

exec p@Process { actor = Break str a }
  = unsafePerformIO $ do
      putStrLn $ withANSI [SetColour Background Red] str
      _ <- getLine
      pure (exec (p { actor = a }))

exec p@Process { actor = Fail str, ..}
  = alarm str $ move (p  { stack = stack :<+>: [] })

exec p@Process {..} = move (p { stack = stack :<+>: [] })

unify :: Process Store Cursor -> Process Store []
-- unify p | dmesg ("\nunify\n  " ++ show p) False = undefined
--unify (Process zf'@(zf :<+>: up@(UnificationProblem s t) : fs) _ _ store a)
--  | dmesg ("\nunify\n  " ++ show t ++ "\n  " ++ show store ++ "\n  " ++ show a) False = undefined
unify p | debug MachineUnify "" p = undefined
unify p@Process { stack = zf :<+>: UnificationProblem date s t : fs, ..} =
  case (expand (headUp store s), expand (headUp store t)) of
    (s, t) | s == t      -> unify (p { stack = zf :<+>: fs })
    (a :%: b, a' :%: b') -> unify (p { stack = zf :<+>: UnificationProblem date a a' : UnificationProblem date b b' : fs })
    (x :.: a, x' :.: a') -> unify (p { stack = zf :<+>: UnificationProblem date a a' : fs })
    (m :$: sg, _) | Just p <- solveMeta m sg t (p { stack = zf :<+>: fs }) -> unify p
    (_, m :$: sg) | Just p <- solveMeta m sg s (p { stack = zf :<+>: fs }) -> unify p
    (_, _) -> unify (p { stack = zf :< UnificationProblem date s t :<+>: fs })
unify p = move p

solveMeta :: Meta   -- The meta (m) we're solving
          -> Subst  -- The substitution (sg) which acts on m
          -> Term   -- The term (t) that must be equal to m :$ sg and depends on ms
          -> Process Store Cursor
          -> Maybe (Process Store Cursor)
solveMeta m (CdB (S0 :^^ _, ph)) tm p@Process{..} = do
  tm <- thickenCdB ph tm
  -- FIXME: do a deep occurs check here to avoid the bug from match
  return (p { store = updateStore m (frnaming stack) tm store })

send :: Channel -> (CdB (Tm ActorMeta), Term) -> Process Store Cursor -> Process Store []
--send ch (tm, term) (Process zfs@(zf :<+>: fs) _ _ _ a)
--  | dmesg ("\nsend " ++ show ch ++ " " ++ show term ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
send ch (tm, term) p
   | debug MachineSend (show ch ++ " " ++ display (frnaming (stack p)) term) p
   = undefined

send ch (tm, term) (p@Process { stack = B0 :<+>: fs, ..})
  = move (p { stack = B0 <>< fs :<+>: [], actor = Send ch tm actor })
send ch (tm, term) (p@Process { stack = zf :< Spawner (childP, q) (r, Hole) :<+>: fs, ..})
  | r == ch =
  let parentP = p { stack = fs, store = today store }
      stack' = zf :< Spawnee (Hole, q) (r, parentP) :< Sent q term <>< stack childP
  in exec (childP { stack = stack', store })
send ch (tm, term) p@Process { stack = zf'@(zf :< Spawnee (Hole, q) (r, parentP)) :<+>: fs, ..}
  | ch == q = exec (p { stack = zf :< Spawnee (Hole, q) (r, parentP { stack = Sent r term : stack parentP }) <>< fs })
  | otherwise = move (p { stack = zf' <>< fs :<+>: [], actor = Send ch tm actor })
send ch (tm, term) p@Process { stack = (zf :< f) :<+>: fs }
  = send ch (tm, term) (p { stack = zf :<+>: (f:fs) })

recv :: Channel -> ActorMeta -> Process Store Cursor -> Process Store []
recv ch v p | debug MachineRecv (show ch ++ " " ++ show v) p = undefined
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
move p | debug MachineMove "" p = undefined

move p@Process { stack = B0 :<+>: fs } = p { stack = fs }
move p@Process { stack = zf :< LeftBranch Hole rp :<+>: fs, ..}
  = let lp = p { stack = fs, store = today store }
    in exec (rp { stack = zf :< RightBranch lp Hole <>< stack rp, store })
move p@Process { stack = zf :< RightBranch lp Hole :<+>: fs, store = st, ..}
  -- | dmesg (show (today st) ++ " " ++ show (store lp)) True
  | today st > store lp
  = let rp = p { stack = fs, store = today st }
    in exec (lp { stack = zf :< LeftBranch Hole rp <>< stack lp, store = st})
move p@Process { stack = zf :< Spawnee (Hole, q) (r, parentP) :<+>: fs, ..}
  = let childP = p { stack = fs, store = today store }
        stack' = zf :< Spawner (childP, q) (r, Hole) <>< stack parentP
    in exec (parentP { stack = stack', store })
move p@Process { stack = zf :< Spawner (childP, q) (r, Hole) :<+>: fs, store = st, ..}
  | today st > store childP
  = let parentP = p { stack = fs, store = today st }
        stack'  = zf :< Spawnee (Hole, q) (r, parentP) <>< stack childP
    in exec (childP { stack = stack', store = st })
move p@Process { stack = zf :< UnificationProblem date s t :<+>: fs, .. }
  | today store > date
  = unify (p { stack = zf :<+>: UnificationProblem (today store) s t : fs })
move p@Process { stack = (zf :< f) :<+>: fs }
  = move (p { stack = zf :<+>: (f : fs) })

debug :: (Traversable t, Collapse t, Display s)
      => MachineStep -> String -> Process s t -> Bool
debug step str p | step `elem` tracing p =
  let (fs', store', env', a') = displayProcess' initNaming p
      p' = unlines $ map ("  " ++) [collapse fs', store', env', a']
  in dmesg ("\n" ++ display initNaming step ++ " " ++ str ++ "\n" ++ p') False
debug step _ p = False
