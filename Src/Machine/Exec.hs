{-# LANGUAGE OverloadedStrings #-}
module Machine.Exec where

import Control.Monad.Reader

import Alarm
import ANSI hiding (withANSI)
import Bwd
import Concrete.Base
import Display
import Doc hiding (render)
import Doc.Render.Terminal
import Elaboration.Pretty ()
import Format
import Hide
import Location (unknown)
import Options
import Pattern
import Pretty
import Scope
import Term
import Thin
import Utils

import Actor
import Machine.Base
import Machine.Display
import Machine.Trace

import System.IO.Unsafe

import Debug.Trace
dmesg = trace

lookupRules :: JudgementForm -> Bwd Frame -> Maybe (AProtocol, (Channel, AActor))
lookupRules jd zf = do
  (_, cha, _) <- (`focusBy` zf) $ \case
    Rules jd' p cha | jd == jd' -> Just (p, cha)
    _ -> Nothing
  pure cha

recordFrame :: Process Shots Store Bwd -> Process Shots Store Bwd
recordFrame p@Process{..} =
  p { logs = instantiate store (extract Simple (length logs) (stack <>> [])) : logs }

-- run an actor
exec :: Process Shots Store Bwd -> Process Shots Store []
-- exec (Process zf _ env store a)
--   | dmesg ("\nexec\n  " ++ unlines (map ("  " ++) [show a])) False
--   = undefined
exec p | debug MachineExec "" p = undefined
exec p@Process { actor = Branch _ a b, ..} =
  let (lroot, rroot) = splitRoot root ""
      rbranch = Process options [] rroot env New b ()
  in exec (p { stack = stack :< LeftBranch Hole rbranch, root = lroot, actor = a})
exec p@Process { actor = Spawn _ em jd spawnerCh actor, ..}
  | Just (jdp, (spawnedCh, spawnedActor)) <- lookupRules jd stack
--  , dmesg (show spawnedActor) True
  = let (subRoot, newRoot) = splitRoot root jd
        spawnee = ( Process options [] subRoot (childEnv env) New spawnedActor ()
                  , spawnedCh)
        spawner = ((spawnerCh, localScope env <>> []), Hole)
    in exec (p { stack = stack :< Spawner (Interface spawnee spawner jd jdp em B0)
               , root = newRoot
               , actor })
exec p@Process { actor = Send _ ch tm a, ..}
  | Just term <- mangleActors options env tm
  = let (subRoot, newRoot) = splitRoot root ""
    in send ch term (p { stack = stack :<+>: []
                       , root = newRoot
                       , actor = a
                       , store = tick store })
exec p@Process { actor = Recv _ ch (x, a), ..}
  = recv ch x (p { stack = stack :<+>: [], actor = a })
exec p@Process { actor = Connect _ ac, ..}
  = connect ac (p { stack = stack :<+>: []})
exec p@Process { actor = m@(Match _ s cls), ..}
  | Just term <- mangleScrutinee s
  = switch term cls
 where

  search :: Bwd Frame -> Int -> Stack -> Int -> Maybe Term
  search B0 i stk bd = Nothing
  search (zf :< f) i stk bd = case f of
      Binding x | i <= 0 -> Nothing
                | otherwise -> search zf (i-1) stk (bd + 1)
      Pushed stk' (DB i', _, t) | stk == stk' && i == i' -> Just (weaks bd t)
      _ -> search zf i stk bd

  mangleScrutinee :: AScrutinee -> Maybe Term
  mangleScrutinee (Term _ t) = mangleActors options env t
  mangleScrutinee (Pair _ sc1 sc2) = (%) <$> mangleScrutinee sc1 <*> mangleScrutinee sc2
  mangleScrutinee (Lookup _ stk t)
    | Just t' <- mangleActors options env t
    = case expand (headUp store t') of
      VX (DB i) _ | Just t' <- search stack i stk 0 -> pure ("Just" #%+ [t'])
      _ :$: _ -> Nothing
      _ -> pure (atom "Nothing" (scope t'))
  mangleScrutinee (Compare _ s t)
    | Just s' <- mangleActors options env s
    , Just t' <- mangleActors options env t
    , Just cmp <- compareUp store s' t'
    = pure (atom (show cmp) (scope s'))
  mangleScrutinee _ = Nothing

  switch :: Term -> [(Pat, AActor)] -> Process Shots Store []
  switch t [] =
    let msg = render (colours options) (Config (termWidth options) Vertical)
         $ unsafeEvalDisplay (frDisplayEnv stack) $ do
          it <- subdisplay (instantiate store t)
          t <- subdisplay t
          m <- asks daEnv >>= \ rh -> withEnv rh $ display m
          pure $ vcat $
                [ "No matching clause for:" <+> it
                , parens ("raw term:" <+> t)
                , "in:"
                , m ]
    in alarm options msg $ move (p { stack = stack :<+>: [] })
  switch t ((pat, a):cs) = case match env [(localScope env, pat,t)] of
    Left True -> switch t cs
    Left False -> move (p { stack = stack :<+>: [] })
    Right env -> exec (p { env = env, actor = a } )

  match :: Env ->
           [(Bwd String -- binders we have gone under
            , Pat
            , Term)] -> Either Bool Env -- Bool: should we keep trying other clauses?
  match env [] = pure env
  match env ((zx, AT x p, tm):xs) = do
    env <- pure $ newActorVar (ActorMeta x) (zx <>> [], tm) env
    match env ((zx, p, tm):xs)
  match env ((zx, MP x ph, tm):xs) | is1s ph = do -- common easy special case
    env <- pure $ newActorVar (ActorMeta x) (zx <>> [], tm) env
    match env xs
  match env ((zx, MP x ph, tm@(CdB t th)):xs) = do
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
      v@(CdB V _) -> case thickenCdB ph v of
        Just v -> pure v
        Nothing -> Left True
      m@(CdB (_ :$ _) _) -> case thickenCdB ph m of
        Just m -> pure m
        Nothing -> Left False
      x -> case expand x of
        AX a ga -> pure (atom a (weeEnd ph))
        s :%: t -> case (instThicken ph s, instThicken ph t) of
          (Left bs, Left bt) -> Left (bs || bt)
          (s, t) -> (%) <$> s <*> t
        (x :.: t) -> (x \\) <$> instThicken (ph -? True) t



exec p@Process { actor = FreshMeta _ cat (av@(ActorMeta x), a), ..} =
  let (xm, root') = meta root x
      xt = xm $: sbstI (length (globalScope env) + length (localScope env))
      env' = newActorVar av (localScope env <>> [], xt) env
  in exec (p { env = env', root = root', actor = a })
exec p@Process { actor = Let _ av@(ActorMeta x) cat tm a, ..}
  | Just term <- mangleActors options env tm
  =  let (xm, root') = meta root x
         env' = newActorVar av (localScope env <>> [], term) env
     in exec (p { env = env', root = root', actor = a })

exec p@Process { actor = Constrain _ s t, ..}
  | Just s' <- mangleActors options env s
  , Just t' <- mangleActors options env t
  -- , dmesg "HERE" True
  -- , dmesg (show env) True
  -- , dmesg (show s ++ " ----> " ++ show s') True
  -- , dmesg (show t ++ " ----> " ++ show t') True
  = unify (p { stack = stack :<+>: [UnificationProblem (today store) s' t'], actor = Win unknown })
exec p@Process { actor = Under _ (Scope (Hide x) a), ..}
  = let scopeSize = length (globalScope env <> localScope env)
        stack' = stack :< Binding (tryAlpha env (getVariable x) ++ "_" ++ show scopeSize)
        env'   = env { localScope = localScope env :< tryAlpha env (getVariable x) }
        actor' = a
    in exec (recordFrame $ p { stack = stack', env = env', actor = actor' })

exec p@Process { actor = Push _ jd (pv, d, t) a, ..}
  | Just t' <- mangleActors options env t
  = let stack' = stack :< Pushed jd (pv, d, t')
        -- if we're pushing on the most local variable, this will all get merged in the trace
        -- so we don't bother generating a logging frame for it
    in exec ((if pv == DB 0 then id else recordFrame) $ p { stack = stack', actor = a })

exec p@Process { actor = Print _ fmt a, ..}
  | Just fmt <- traverse (traverse $ mangleActors options env) fmt
  =  unsafePerformIO $ do
      putStrLn $ format [SetColour Background Magenta] p fmt
      pure (exec (p { actor = a }))

exec p@Process { actor = Break _ fmt a, ..}
  = unsafePerformIO $ do
      when (MachineBreak `elem` tracing p) $ do
        whenJust (traverse (traverse $ mangleActors options env) fmt) $ \ fmt -> do
          putStrLn $ format [SetColour Background Red] p fmt
          () <$ getLine
      pure (exec (p { actor = a }))

exec p@Process { actor = Fail r fmt, ..}
  = let msg = evalError p fmt
        act = Fail r [StringPart msg]
    in  alarm options msg $ move (p { stack = stack :<+>: []
                                    , actor = act
                                    })

exec p@Process { actor = Note _ a, .. }
  = exec (p { stack = stack :< Noted, actor = a})

exec p@Process {..} = move (p { stack = stack :<+>: [] })

evalError :: Process log Store Bwd -> [Format Directive Debug ACTm] -> String
evalError p@Process{..} fmt
  = case traverse (traverse $ mangleActors options env) fmt of
      Just fmt -> format [] p fmt
      Nothing -> case evalDisplay (frDisplayEnv stack) (subdisplay fmt) of
        Left grp -> "Error " ++ show grp ++ " in the error " ++ show fmt
        Right str -> render (colours options) (Config (termWidth options) Vertical) str

format :: [Annotation] -> Process log Store Bwd -> [Format Directive Debug Term] -> String
format ann p@Process{..} fmt
  = render (colours options) (Config (termWidth options) Vertical)
  $ unsafeEvalDisplay (frDisplayEnv stack)
  $ fmap (withANSI ann)
  $ subdisplay
  $ insertDebug p
  $ instantiate store fmt

unify :: Process Shots Store Cursor -> Process Shots Store []
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
          -> Process log Store Cursor
          -> Maybe (Process log Store Cursor)
solveMeta m (CdB (S0 :^^ _) ph) tm p@Process{..} = do
  tm <- thickenCdB ph tm
  -- FIXME: do a deep occurs check here to avoid the bug from match
  return (p { store = updateStore m (objectNaming $ frDisplayEnv stack) tm store })

connect :: AConnect
        -> Process Shots Store Cursor
        -> Process Shots Store []
connect ac@(AConnect ch1 th ch2 n) p@Process { stack = zf :< Sent q tm :<+>: fs, ..}
  | q == ch1 = send ch2 (snd tm *^ th')
               (p { stack = zf <>< fs :<+>: []
                  , actor = aconnect unknown ch1 th ch2 (n-1)})
  | q == ch2 = send ch1 (snd tm *^ th')
               (p { stack = zf <>< fs :<+>: []
                  , actor = aconnect unknown ch1 th ch2 (n-1)})
  where th' = ones (length (globalScope env)) <> th
connect ac p@Process { stack = zf'@(zf :< Spawnee intf) :<+>: fs, ..}
  = move (p { stack = zf' <>< fs :<+>: []})
connect ac p@Process { stack = zf :< f :<+>: fs}
  = connect ac (p { stack = zf :<+>: (f:fs) })

send :: Channel -> Term
     -> Process Shots Store Cursor
     -> Process Shots Store []
--send ch term (Process zfs@(zf :<+>: fs) _ _ _ a)
--  | dmesg ("\nsend " ++ show ch ++ " " ++ show term ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
-- send (Channel ch) term p
--   | debug MachineSend (unwords [ch, show term]) p
--   = undefined

send ch term p@Process { stack = B0 :<+>: fs, ..}
  -- TODO: use the range of the send?
  = let a = Fail unknown [StringPart ("Couldn't find channel " ++ rawChannel ch)]
    in exec (p { stack = B0 <>< fs, actor = a })
send ch term
  p@Process { stack = zf :< Spawner (Interface (childP, q) (rxs@(r, _), Hole) jd jdp em tr) :<+>: fs, ..}
  | r == ch =
  let parentP = p { stack = fs, store = New, logs = () }
      stack' = zf :< Spawnee (Interface (Hole, q) (rxs, parentP) jd jdp em (tr :< term))
                  :< Sent q ([], term) <>< stack childP
      p' = recordFrame (childP { stack = stack', store, logs })
  in debug MachineSend (pretty ch) p' `seq` exec p'
send ch term
  p@Process { stack = zf'@(zf :< Spawnee (Interface (Hole, q) (rxs@(r, xs), parentP) jd jdp em tr)) :<+>: fs
            , ..}
  | ch == q =
  let parentP' = parentP { stack = Sent r (xs, term) : stack parentP, store = New }
      stack'   = zf :< Spawnee (Interface (Hole, q) (rxs, parentP') jd jdp em (tr :< term)) <>< fs
      p' = recordFrame (p { stack = stack' })
  in debug MachineSend (pretty ch) p' `seq` exec p'
  | otherwise
  = let a = Fail unknown [StringPart ("Couldn't find channel " ++ rawChannel ch)]
    in exec (p { stack = zf' <>< fs, actor = a })
send ch term p@Process { stack = (zf :< f) :<+>: fs }
  = send ch term (p { stack = zf :<+>: (f:fs) })

recv :: Channel -> Binder ActorMeta
     -> Process Shots Store Cursor
     -> Process Shots Store []
recv ch v p | debug MachineRecv (hsep [ pretty ch, pretty v ]) p = undefined
recv ch x p@Process { stack = B0 :<+>: fs, ..}
  = move (p { stack = B0 <>< fs :<+>: [], actor = Recv unknown ch (x, actor) })
recv ch x p@Process { stack = zf :< Sent q y :<+>: fs, ..}
  | ch == q
  = let env' = case x of
                 Unused -> env
                 Used x -> newActorVar x y env
    in exec (p { stack = zf <>< fs, env = env' })
recv ch x
  p@Process { stack = zf'@(zf :< Spawnee (Interface (Hole, q) (rxs, parentP) _ _ _ _)) :<+>: fs, ..}
  = move (p { stack = zf' <>< fs :<+>: [], actor = Recv unknown ch (x, actor) })
recv ch x
  p@Process { stack = zf'@(zf :< Spawner (Interface (childP, q) ((r, xs), Hole) _ _ _ _)) :<+>: fs, ..}
  | ch == r
  = move (p { stack = zf' <>< fs :<+>: [], actor = Recv unknown ch (x, actor) })
recv ch x p@Process { stack = zf :< f :<+>: fs }
  = recv ch x (p { stack = zf :<+>: (f:fs) })

-- find the next thing to run
move :: Process Shots Store Cursor -> Process Shots Store []
-- move (Process zfs _ _ store a)
-- | dmesg ("\nmove\n  " ++ show zfs ++ "\n  " ++ show store ++ "\n  " ++ show a) False = undefined
move p | debug MachineMove "" p = undefined

move p@Process { stack = B0 :<+>: fs } = p { stack = fs }
move p@Process { stack = zf :< LeftBranch Hole rp :<+>: fs, ..}
  = let lp = p { stack = fs, store = StuckOn (today store), logs = () }
    in exec (rp { stack = zf :< RightBranch lp Hole <>< stack rp, store, logs })
move p@Process { stack = zf :< RightBranch lp Hole :<+>: fs, store = st, ..}
  | StuckOn (today st) > store lp
  = let rp = p { stack = fs, store = StuckOn (today st), logs = () }
    in exec (lp { stack = zf :< LeftBranch Hole rp <>< stack lp, store = st, logs})
move p@Process { stack = zf :< Spawnee (Interface (Hole, q) (rxs, parentP) jd jdp em tr) :<+>: fs, ..}
  = let childP = p { stack = fs, store = StuckOn (today store), logs = () }
        stack' = zf :< Spawner (Interface (childP, q) (rxs, Hole) jd jdp em tr) <>< stack parentP
    in exec (parentP { stack = stack', store, logs })
move p@Process { stack = zf :< Spawner (Interface (childP, q) (rxs, Hole) jd jdp em tr) :<+>: fs
               , store = st, ..}
  | StuckOn (today st) > store childP
  = let parentP = p { stack = fs, store = StuckOn (today st), logs = () }
        stack'  = zf :< Spawnee (Interface (Hole, q) (rxs, parentP) jd jdp em tr) <>< stack childP
    in exec (childP { stack = stack', store = st, logs })
move p@Process { stack = zf :< UnificationProblem date s t :<+>: fs, .. }
  | today store > date
  = unify (p { stack = zf :<+>: UnificationProblem (today store) s t : fs })
move p@Process { stack = (zf :< f) :<+>: fs }
  = move (p { stack = zf :<+>: (f : fs) })

debug :: (Show (t Frame), Traversable t, Collapse t, Display0 s)
      => MachineStep -> Doc Annotations -> Process log s t -> Bool
debug step str p | step `elem` tracing p = -- dmesg (show step ++ ": " ++ show p) $
  let (fs', store', env', a') = unsafeEvalDisplay initDEnv $ displayProcess' p
      p' = indent 2 $ vcat $ [collapse fs', store', env', a']
      step' = keyword (pretty step)
      msg = render (colours $ options p) (initConfig 0) $ vcat [mempty, step' <+> str, p']
  in dmesg msg False
debug step _ p = False
