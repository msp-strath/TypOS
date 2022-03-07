module Machine.Exec where

import Control.Monad.Reader

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

lookupRules :: JudgementForm -> Bwd Frame -> Maybe (Channel, Actor)
lookupRules jd zf = do
  (_, cha, _) <- (`focusBy` zf) $ \case
    Rules jd' cha | jd == jd' -> Just cha
    _ -> Nothing
  pure cha

-- run an actor
exec :: Process Store Bwd -> Process Store []
-- exec (Process zf _ env store a)
--   | dmesg ("\nexec\n  " ++ unlines (map ("  " ++) [show a])) False
--   = undefined
exec p | debug MachineExec "" p = undefined
exec p@Process { actor = a :|: b, ..} =
  let (lroot, rroot) = splitRoot root ""
      rbranch = Process tracing [] rroot env (today store) b judgementform
  in exec (p { stack = stack :< LeftBranch Hole rbranch, root = lroot, actor = a})
exec p@Process { actor = Spawn jd spawnerCh actor, ..}
  | Just (spawnedCh, spawnedActor) <- lookupRules jd stack
--  , dmesg (show spawnedActor) True
  = let (subRoot, newRoot) = splitRoot root jd
        spawnee = ( Process tracing [] subRoot (childEnv env) (today store) spawnedActor jd
                  , spawnedCh)
        spawner = ((spawnerCh, localScope env <>> []), Hole)
    in exec (p { stack = stack :< Spawner (Interface spawnee spawner)
               , root = newRoot
               , actor })
exec p@Process { actor = Send ch tm a, ..}
  | Just term <- mangleActors env tm
  = let (subRoot, newRoot) = splitRoot root ""
    in send ch (tm, term) (p { stack = stack :<+>: [], root = newRoot, actor = a })
exec p@Process { actor = Recv ch (x, a), ..}
  = recv ch x (p { stack = stack :<+>: [], actor = a })
exec p@Process { actor = m@(Match s cls), ..}
  | Just term <- mangleActors env s
  = switch term cls
 where

  switch :: Term -> [(Pat, Actor)] -> Process Store []
  switch t [] =
    let msg = unsafeEvalDisplay (frDisplayEnv stack) $ do
          it <- subdisplay (instantiate store t)
          t <- subdisplay t
          (s, cls) <- asks daEnv >>= \ rh -> withEnv rh $ do
            s <- subdisplay s
            cls <- traverse display cls
            pure (s, cls)
          pure $ unlines $
                [ "No matching clause for: " ++ it
                , "(raw term: " ++ t ++ ")"
                , "in: case " ++ s
                ] ++ zipWith (\ cs cl -> "  " ++ cs ++ cl) ("{ ":repeat "; ") cls
                  ++ ["  }"]
    in alarm msg $ move (p { stack = stack :<+>: [] })
  switch t ((pat, a):cs) = case match env [(localScope env, pat,t)] of
    Left True -> switch t cs
    Left False -> move (p { stack = stack :<+>: [] })
    Right env -> exec (p { env = env, actor = a } )

  match :: Env ->
           [(Bwd String -- binders we have gone under
            , Pat
            , Term)] -> Either Bool Env -- Bool: should we keep trying other clauses?
  match env [] = pure env
  match env ((zx, MP x ph, tm):xs) | is1s ph = do -- common easy special case
    env <- pure $ newActorVar (ActorMeta x) (zx <>> [], tm) env
    match env xs
  match env ((zx, MP x ph, tm@(CdB (t, th))):xs) = do
    let g = bigEnd th - bigEnd ph
    -- we can do better: t may not depend on disallowed things until definitions are expanded
    tm <- instThicken (ones g <> ph) tm
    env <- pure $ newActorVar (ActorMeta x) ((ph ?< zx) <>> [], tm) env
    match env xs
  match env ((zx, pat, tm):xs) = case (pat, expand (headUp store tm)) of
    (HP, _) -> match env xs
    (GP, _) -> Left True
    (_, (_ :$: _)) -> Left False
    (VP i, VX j _) | i == j -> match env xs
    (AP a, AX b _) | a == b -> match env xs
    (PP p q, s :%: t) -> match env ((zx,p,s):(zx,q,t):xs)
    (BP (Hide x) p, y :.: t) -> match (declareAlpha (x, Hide y) env) ((zx :< x,p,t):xs)
    _ -> Left True

  instThicken :: Th -> Term -> Either Bool Term
  instThicken ph t = case headUp store t of
      v@(CdB (V, _)) -> case thickenCdB ph v of
        Just v -> pure v
        Nothing -> Left True
      m@(CdB (_ :$ _,_)) -> case thickenCdB ph m of
        Just m -> pure m
        Nothing -> Left False
      x -> case expand x of
        AX a ga -> pure (atom a (weeEnd ph))
        s :%: t -> case (instThicken ph s, instThicken ph t) of
          (Left bs, Left bt) -> Left (bs || bt)
          (s, t) -> (%) <$> s <*> t
        (x :.: t) -> (x \\) <$> instThicken (ph -? True) t



exec p@Process { actor = FreshMeta (av@(ActorMeta x), a), ..} =
  let (xm, root') = meta root x
      xt = xm $: sbstI (length (globalScope env) + length (localScope env))
      env' = newActorVar av (localScope env <>> [], xt) env
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
  = let stack' = stack :< Binding (tryAlpha env x ++ "_" ++ show (length (globalScope env <> localScope env)))
        env'   = env { localScope = localScope env :< tryAlpha env x }
        actor' = a
    in exec (p { stack = stack', env = env', actor = actor' })

exec p@Process { actor = Push jd (pv, t) a, ..}
  | Just t' <- mangleActors env t
  = let stack' = stack :< Pushed jd (pv, t')
    in exec (p { stack = stack', actor = a })

exec p@Process { actor = Lookup t (av, a) b, ..}
  | Just t' <- mangleActors env t
  = case expand (headUp store t') of
      VX (DB i) _ | Just t' <- search stack i judgementform 0 ->
        let env' = newActorVar av (localScope env <>> [], t') env
        in exec (p {actor = a, env = env'})
      _ :$: _ -> move (p { stack = stack :<+>: [] })
      _ -> exec (p {actor = b})
  where

    search :: Bwd Frame -> Int -> JudgementForm -> Int -> Maybe Term
    search B0 i jd bd = Nothing
    search (zf :< f) i jd bd = case f of
      Binding x | i <= 0 -> Nothing
                | otherwise -> search zf (i-1) jd (bd + 1)
      Pushed jd' (DB i', t) | jd == jd' && i == i' -> Just (weaks bd t)
      _ -> search zf i jd bd

exec p@Process { actor = Print fmt a, ..}
  | Just format <- traverse (traverse $ mangleActors env) fmt
  =  unsafePerformIO $ do
      putStrLn $ withANSI [SetColour Background Magenta]
               $ unsafeEvalDisplay (frDisplayEnv stack)
               $ subdisplay
               $ insertDebug p
               $ instantiate store format
      _ <- getLine
      pure (exec (p { actor = a }))

exec p@Process { actor = Break str a }
  = unsafePerformIO $ do
      when (MachineBreak `elem` tracing p) $ do
        putStrLn $ withANSI [SetColour Background Red] str
        () <$ getLine
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
  return (p { store = updateStore m (objectNaming $ frDisplayEnv stack) tm store })

send :: Channel -> (CdB (Tm ActorMeta), Term) -> Process Store Cursor -> Process Store []
--send ch (tm, term) (Process zfs@(zf :<+>: fs) _ _ _ a)
--  | dmesg ("\nsend " ++ show ch ++ " " ++ show term ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
-- send (Channel ch) (tm, term) p
--   | debug MachineSend (unwords [ch, show (tm, term)]) p
--   = undefined

send ch (tm, term) (p@Process { stack = B0 :<+>: fs, ..})
  = move (p { stack = B0 <>< fs :<+>: [], actor = Send ch tm actor })
send ch (tm, term)
  p@Process { stack = zf :< Spawner (Interface (childP, q) (rxs@(r, _), Hole)) :<+>: fs, ..}
  | r == ch =
  let parentP = p { stack = fs, store = today store }
      stack' = zf :< Spawnee (Interface (Hole, q) (rxs, parentP))
                  :< Sent q ([], term) <>< stack childP
      p' = childP { stack = stack', store }
  in debug MachineSend (rawChannel ch) p' `seq` exec p'
send ch (tm, term)
  p@Process { stack = zf'@(zf :< Spawnee (Interface (Hole, q) (rxs@(r, xs), parentP))) :<+>: fs
            , ..}
  | ch == q =
  let parentP' = parentP { stack = Sent r (xs, term) : stack parentP }
      stack'   = zf :< Spawnee (Interface (Hole, q) (rxs, parentP')) <>< fs
      p' = p { stack = stack' }
  in debug MachineSend (rawChannel ch) p' `seq` exec p'
  | otherwise = move (p { stack = zf' <>< fs :<+>: [], actor = Send ch tm actor })
send ch (tm, term) p@Process { stack = (zf :< f) :<+>: fs }
  = send ch (tm, term) (p { stack = zf :<+>: (f:fs) })

recv :: Channel -> ActorMeta -> Process Store Cursor -> Process Store []
recv ch v p | debug MachineRecv (show ch ++ " " ++ show v) p = undefined
-- recv ch v (zfs, _, _, _, a)
 -- | dmesg ("\nrecv " ++ show ch ++ " " ++ show v ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
recv ch x p@Process { stack = B0 :<+>: fs, ..}
  = move (p { stack = B0 <>< fs :<+>: [], actor = Recv ch (x, actor) })
recv ch x p@Process { stack = zf :< Sent q y :<+>: fs, ..}
  | ch == q
  = let env' = newActorVar x y env in -- TODO: is this right?
    exec (p { stack = zf <>< fs, env = env' })
recv ch x
  p@Process { stack = zf'@(zf :< Spawnee (Interface (Hole, q) (rxs, parentP))) :<+>: fs, ..}
  = move (p { stack = zf' <>< fs :<+>: [], actor = Recv ch (x, actor) })
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
move p@Process { stack = zf :< Spawnee (Interface (Hole, q) (rxs, parentP)) :<+>: fs, ..}
  = let childP = p { stack = fs, store = today store }
        stack' = zf :< Spawner (Interface (childP, q) (rxs, Hole)) <>< stack parentP
    in exec (parentP { stack = stack', store })
move p@Process { stack = zf :< Spawner (Interface (childP, q) (rxs, Hole)) :<+>: fs
               , store = st, ..}
  | today st > store childP
  = let parentP = p { stack = fs, store = today st }
        stack'  = zf :< Spawnee (Interface (Hole, q) (rxs, parentP)) <>< stack childP
    in exec (childP { stack = stack', store = st })
move p@Process { stack = zf :< UnificationProblem date s t :<+>: fs, .. }
  | today store > date
  = unify (p { stack = zf :<+>: UnificationProblem (today store) s t : fs })
move p@Process { stack = (zf :< f) :<+>: fs }
  = move (p { stack = zf :<+>: (f : fs) })

debug :: (Show (t Frame), Traversable t, Collapse t, Display0 s)
      => MachineStep -> String -> Process s t -> Bool
debug step str p | step `elem` tracing p = -- dmesg (show step ++ ": " ++ show p) $
  let (fs', store', env', a') = unsafeEvalDisplay initDEnv $ displayProcess' p
      p' = unlines $ map ("  " ++) [collapse fs', store', env', a']
  in dmesg ("\n" ++ (unsafeEvalDisplay initDEnv $ subdisplay step) ++ " " ++ str ++ "\n" ++ p') False
debug step _ p = False
