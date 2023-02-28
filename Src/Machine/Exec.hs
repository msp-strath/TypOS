{-# LANGUAGE OverloadedStrings #-}
module Machine.Exec where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Unelaboration (nameSel)

import Control.Monad.Reader

import Alarm
import ANSI hiding (withANSI)
import Bwd
import Concrete.Base
import Display
import Elaboration.Pretty ()
import Format
import Hide
import Location (unknown)
import Options
import Pretty
import Scope
import Term
import Thin
import Utils

import Actor
import Machine.Base
import Machine.Display
import Machine.Matching
import Machine.Trace

import System.IO.Unsafe

import Debug.Trace
import Operator.Eval

dmesg = trace

lookupRules :: JudgementName -> Bwd Frame -> Maybe (AProtocol, (Channel, AActor))
lookupRules jd zf = do
  (_, cha, _) <- (`focusBy` zf) $ \case
    Rules jd' p cha | jd == jd' -> Just (p, cha)
    _ -> Nothing
  pure cha

mkHeadUpData :: Process a Store Bwd -> HeadUpData
mkHeadUpData Process{..} =
  let what m = Map.lookup m (solutions store) >>= snd
  in HeadUpData (mkOpTable stack) store options env what

recordFrame :: Process Shots Store Bwd -> Process Shots Store Bwd
recordFrame p@Process{..} =
  let dat = mkHeadUpData (p{options = options { quiet = True }})
  in p { logs = normalise dat (extract Simple (length logs) (stack <>> [])) : logs }

-- run an actor
exec :: Process Shots Store Bwd -> Process Shots Store []
-- exec (Process zf _ env store a)
--   | dmesg ("\nexec\n  " ++ unlines (map ("  " ++) [show a])) False
--   = undefined
exec p | debug MachineExec "" p = undefined
exec p@Process { actor = Branch _ a b, ..} =
  let (lroot, rroot) = splitRoot root ""
      rbranch = Process { options
                        , stack = []
                        , root = rroot
                        , env
                        , store = New
                        , actor = b
                        , logs = ()
                        , geas = rroot
                        }
  in exec (p { stack = stack :< LeftBranch Hole rbranch
             , root = lroot
             , actor = a
             , store = defineGuard geas (Set.fromList [lroot, rroot]) store
             , geas = lroot
             })
exec p@Process { actor = Spawn _ em jd spawnerCh actor, ..}
  | Just (jdp, (spawnedCh, spawnedActor)) <- lookupRules jd stack
--  , dmesg (show spawnedActor) True
  = let (subRoot, newRoot) = splitRoot root jd
        spawnee = ( Process { options
                            , stack = []
                            , root = subRoot
                            , env = childEnv env
                            , store = New
                            , actor = spawnedActor
                            , logs = ()
                            , geas = subRoot
                            }
                  , spawnedCh)
        spawner = ((spawnerCh, localScope env <>> []), Hole)
    in exec (p { stack = stack :< Spawner (Interface spawnee spawner jd jdp em B0)
               , root = newRoot
               , actor })
exec p@Process { actor = Send _ ch mv tm a, ..}
  | Just term <- mangleActors options env tm
  =  send ch (mv >>= (`Map.lookup` subjectGuards env)) term
          (p { stack = stack :<+>: []
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

  dat = mkHeadUpData p

  search :: Bwd Frame -> Int -> Stack -> Int -> Maybe Term
  search B0 i stk bd = Nothing
  search (zf :< f) i stk bd = case f of
      Binding x | i <= 0 -> Nothing
                | otherwise -> search zf (i-1) stk (bd + 1)
      Pushed stk' (DB i', _, t) | stk == stk' && i == i' -> Just (weaks bd t)
      _ -> search zf i stk bd

  mangleScrutinee :: AScrutinee -> Maybe Term
  mangleScrutinee (SubjectVar _ t) = mangleActors options env t
  mangleScrutinee (Term _ t) = mangleActors options env t
  mangleScrutinee (Pair _ sc1 sc2) = (%) <$> mangleScrutinee sc1 <*> mangleScrutinee sc2
  mangleScrutinee (Lookup _ stk t)
    | Just t' <- mangleActors options env t
    = case expand (headUp dat t') of
      VX (DB i) _ | Just t' <- search stack i stk 0 -> pure ("Just" #%+ [t'])
      x | stuck x -> Nothing
      _ -> pure (atom "Nothing" (scope t'))
  mangleScrutinee (Compare _ s t)
    | Just s' <- mangleActors options env s
    , Just t' <- mangleActors options env t
    , Just cmp <- compareUp dat s' t'
    = pure (atom (show cmp) (scope s'))
  mangleScrutinee _ = Nothing

  switch :: Term -> [(Pat, AActor)] -> Process Shots Store []
  switch t [] =
    let msg = renderWith (renderOptions options)
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
  switch t ((pat, a):cs) = case match (headUp dat) initMatching (Problem (localScope env) pat t) of
    (t, Left Mismatch) -> switch t cs
    (t, Left DontKnow) -> move (p { stack = stack :<+>: [] })
    (t, Right mat) -> case matchingCase mat (root, env) of
        (root, env) -> exec (p { env, root, actor = a } )

exec p@Process { actor = FreshMeta _ cat (av@(ActorMeta _ x), a), ..} =
  let (xm, root') = meta root x
      xt = xm $: sbstI (length (globalScope env) + length (localScope env))
      store' = declareMeta xm (objectNaming $ frDisplayEnv stack) store
      env' = newActorVar av (localScope env <>> [], xt) env
  in exec (p { env = env', store = store', root = root', actor = a })
exec p@Process { actor = Let _ av@(ActorMeta _ x) cat tm a, ..}
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
  = let dat = mkHeadUpData p in
    unify dat (p { stack = stack :<+>: [UnificationProblem (today store) s' t'], actor = Win unknown })
exec p@Process { actor = Under _ _ (Scope (Hide x) a), ..}
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

exec p@Process { actor = Win _, .. } | Nothing <- Map.lookup geas (guards store) =
  move (p { stack = stack :<+>: [], store = tick (defineGuard geas Set.empty store) })

exec p@Process {..} = move (p { stack = stack :<+>: [] })

evalError :: Process log Store Bwd -> [Format Directive Debug ACTm] -> String
evalError p@Process{..} fmt
  = case traverse (traverse $ mangleActors options env) fmt of
      Just fmt -> format [] p fmt
      Nothing -> case evalDisplay (frDisplayEnv stack) (subdisplay fmt) of
        Left grp -> "Error " ++ show grp ++ " in the error " ++ show fmt
        Right doc -> renderWith (renderOptions options) doc

format :: [Annotation] -> Process log Store Bwd -> [Format Directive Debug Term] -> String
format ann p@Process{..} fmt
  = renderWith (renderOptions options)
  $ unsafeEvalDisplay (frDisplayEnv stack)
  $ fmap (withANSI ann)
  $ subdisplay
  $ insertDebug p
  $ map (followDirectives $ mkHeadUpData p) fmt

unify :: HeadUpData -> Process Shots Store Cursor -> Process Shots Store []
-- unify p | dmesg ("\nunify\n  " ++ show p) False = undefined
--unify (Process zf'@(zf :<+>: up@(UnificationProblem s t) : fs) _ _ store a)
--  | dmesg ("\nunify\n  " ++ show t ++ "\n  " ++ show store ++ "\n  " ++ show a) False = undefined
unify dat p | debug MachineUnify "" p = undefined
unify dat p@Process { stack = zf :<+>: UnificationProblem date s t : fs, ..} =
  case (expand (headUp dat s), expand (headUp dat t)) of
    (s, t) | s == t      -> unify dat (p { stack = zf :<+>: fs })
    (a :%: b, a' :%: b') -> unify dat (p { stack = zf :<+>: UnificationProblem date a a' : UnificationProblem date b b' : fs })
    (x :.: a, x' :.: a') -> unify dat (p { stack = zf :<+>: UnificationProblem date a a' : fs })
    (m :$: sg, _)
      | Just p <- solveMeta m sg t (p { stack = zf :<+>: fs })
      -> unify dat p
    (_, m :$: sg)
      | Just p <- solveMeta m sg s (p { stack = zf :<+>: fs })
      -> unify dat p
    (s, t) -> unify dat (p { stack = zf :< UnificationProblem date (contract s) (contract t) :<+>: fs })
unify dat p = move p

deepCheck :: HeadUpData
          -> Th    -- D0 <= D
          -> Term  -- D
          -> Process log Store Cursor
          -> Maybe (Term -- D0
                   , Process log Store Cursor)
deepCheck dat th tm p =
  let (CdB t ph) = headUp dat tm in
  let (ph', _, th') = pullback th ph in
  if is1s th' then pure (CdB t ph', p) else case t of
    V -> Nothing
    A at -> error "The IMPOSSIBLE happened in deepCheck"
    P k rp -> splirp (CdB rp ph) $ \a b -> do
      (a, p) <- deepCheck dat th a p
      (b, p) <- deepCheck dat th b p
      pure (P k $^ (a <&> b), p)
    (nm := b) :. sc -> do (sc, p) <- deepCheck dat (th -? b) (CdB sc (ph -? b)) p
                          pure (unhide nm \\ sc, p)
    m :$ sg -> do (sg', th', p) <- pure $ strengthenSbst dat th sg p
                  let (xm, root') = meta (root p) (fst $ last $ unMeta m)
                  let naming = fst $ fromJust $ Map.lookup m (solutions $ store p)
                  let store' = declareMeta xm (nameSel th' naming) (store p)
                  let p' = p { root = root' }
                  let store'' = updateStore m (xm $: sbstI (weeEnd th') *^ th') store'
                  pure ((xm :$) $^ sg', p' { store = store'' })

strengthenSbst :: HeadUpData
               -> Th        -- D0 <= D
               -> Sbst Meta -- G --> D
               -> Process log Store Cursor
               -> ( Subst   -- G0 --> D0
                  , Th      -- G0 <= G
                  , Process log Store Cursor)
strengthenSbst dat th sg p | is1s th = (CdB sg th, ones (sbstDom sg), p)
strengthenSbst dat th (S0 :^^ 0) p = (CdB (S0 :^^ 0) (none (weeEnd th)), ones 0, p)
strengthenSbst dat th (ST (CdB sg ps :<>: CdB (nm := t) xi) :^^ 0) p =
  let (ps', _, th') = pullback th ps in
  let (sg', ph, p') = strengthenSbst dat th' sg p in
  let sg'' = sg' *^ ps' in
  case deepCheck dat th (CdB t xi) p' of
    Nothing -> (sg'', ph -? False, p')
    Just (t', p) -> (sbstT sg'' ((nm :=) $^ t'), ph -? True, p)
strengthenSbst dat th (sg :^^ n) p =
  let (th', b) = thun th in
  let (sg', ph, p') = strengthenSbst dat th' (sg :^^ (n-1)) p in
  (if b then sbstW sg' (ones 1) else sg', ph -? b, p')

solveMeta :: Meta   -- The meta (m) we're solving
          -> Subst  -- The substitution (sg) which acts on m
          -> Term   -- The term (t) that must be equal to m :$ sg and depends on ms
          -> Process log Store Cursor
          -> Maybe (Process log Store Cursor)
solveMeta m (CdB (S0 :^^ _) th) tm p@Process{..} = do
  let dat = mkHeadUpData (p{ stack = let (fs :<+>: _) = stack in fs})
  (tm, p) <- deepCheck dat th tm p
  return (p { store = updateStore m tm store })


connect :: AConnect
        -> Process Shots Store Cursor
        -> Process Shots Store []
connect ac@(AConnect ch1 th ch2 n) p@Process { stack = zf :< Sent q gd tm :<+>: fs, ..}
  | q == ch1 = send ch2 gd (snd tm *^ th')
               (p { stack = zf <>< fs :<+>: []
                  , actor = aconnect unknown ch1 th ch2 (n-1)})
  | q == ch2 = send ch1 gd (snd tm *^ th')
               (p { stack = zf <>< fs :<+>: []
                  , actor = aconnect unknown ch1 th ch2 (n-1)})
  where th' = ones (length (globalScope env)) <> th
connect ac p@Process { stack = zf'@(zf :< Spawnee intf) :<+>: fs, ..}
  = move (p { stack = zf' <>< fs :<+>: []})
connect ac p@Process { stack = zf :< f :<+>: fs}
  = connect ac (p { stack = zf :<+>: (f:fs) })

send :: Channel -> Maybe Guard -> Term
     -> Process Shots Store Cursor
     -> Process Shots Store []
--send ch term (Process zfs@(zf :<+>: fs) _ _ _ a)
--  | dmesg ("\nsend " ++ show ch ++ " " ++ show term ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
-- send (Channel ch) term p
--   | debug MachineSend (unwords [ch, show term]) p
--   = undefined

send ch gd term p@Process { stack = B0 :<+>: fs, ..}
  -- TODO: use the range of the send?
  = let a = Fail unknown [StringPart ("Couldn't find channel " ++ rawChannel ch)]
    in exec (p { stack = B0 <>< fs, actor = a })
send ch gd term
  p@Process { stack = zf :< Spawner (Interface (childP, q) (rxs@(r, _), Hole) jd jdp em tr) :<+>: fs, ..}
  | r == ch =
  -- claim : gd should be Nothing - we do not communicate unvalidated terms to our parents
  let parentP = p { stack = fs, store = New, logs = () }
      stack' = zf :< Spawnee (Interface (Hole, q) (rxs, parentP) jd jdp em (tr :< term))
                  :< Sent q gd ([], term) <>< stack childP
      p' = recordFrame (childP { stack = stack', store, logs })
  in debug MachineSend (pretty ch) p' `seq` exec p'
send ch gd term
  p@Process { stack = zf'@(zf :< Spawnee (Interface (Hole, q) (rxs@(r, xs), parentP) jd jdp em tr)) :<+>: fs
            , ..}
  | ch == q =
  let parentP' = parentP { stack = Sent r gd (xs, term) : stack parentP, store = New }
      stack'   = zf :< Spawnee (Interface (Hole, q) (rxs, parentP') jd jdp em (tr :< term)) <>< fs
      p' = recordFrame (p { stack = stack' })
  in debug MachineSend (pretty ch) p' `seq` exec p'
  | otherwise
  = let a = Fail unknown [StringPart ("Couldn't find channel " ++ rawChannel ch)]
    in exec (p { stack = zf' <>< fs, actor = a })
send ch gd term p@Process { stack = (zf :< f) :<+>: fs }
  = send ch gd term (p { stack = zf :<+>: (f:fs) })

recv :: Channel -> Binder ActorMeta
     -> Process Shots Store Cursor
     -> Process Shots Store []
recv ch v p | debug MachineRecv (hsep [ pretty ch, pretty v ]) p = undefined
recv ch x p@Process { stack = B0 :<+>: fs, ..}
  = move (p { stack = B0 <>< fs :<+>: [], actor = Recv unknown ch (x, actor) })
recv ch x p@Process { stack = zf :< Sent q gd y :<+>: fs, ..}
  | ch == q
  = let env' = case x of
                 Unused -> env
                 Used x -> case x of
                   ActorMeta ASubject v -> guardSubject v y geas $ newActorVar x y env
                   ActorMeta ACitizen v -> newActorVar x y env
        store' = case gd of
                   Nothing -> store
                   Just gd -> defineGuard gd (Set.singleton geas) store
    in exec (p { stack = zf <>< fs, env = env', store = store' })
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
move p@Process { stack = zf :< LeftBranch Hole rp :<+>: fs, store = st, ..}
  | StuckOn (today st) > store rp
  = let lp = p { stack = fs, store = status fs actor (today st), logs = () }
    in exec (rp { stack = zf :< RightBranch lp Hole <>< stack rp, store = st, logs })
move p@Process { stack = zf :< RightBranch lp Hole :<+>: fs, store = st, ..}
  | StuckOn (today st) > store lp
  = let rp = p { stack = fs, store = status fs actor (today st), logs = () }
    in exec (lp { stack = zf :< LeftBranch Hole rp <>< stack lp, store = st, logs})
move p@Process { stack = zf :< Spawnee (Interface (Hole, q) (rxs, parentP) jd jdp em tr) :<+>: fs, store = st, ..}
  -- no guard here! We've reached the end of the stack frame
  = let childP = p { stack = fs, store = status fs actor (today st), logs = () }
        stack' = zf :< Spawner (Interface (childP, q) (rxs, Hole) jd jdp em tr) <>< stack parentP
    in exec (parentP { stack = stack', store = st, logs })
move p@Process { stack = zf :< Spawner (Interface (childP, q) (rxs, Hole) jd jdp em tr) :<+>: fs
               , store = st, ..}
  | StuckOn (today st) > store childP
  = let parentP = p { stack = fs, store = status fs actor (today st), logs = () }
        stack'  = zf :< Spawnee (Interface (Hole, q) (rxs, parentP) jd jdp em tr) <>< stack childP
    in exec (childP { stack = stack', store = st, logs })
move p@Process { stack = zf :< UnificationProblem date s t :<+>: fs, .. }
  | today store > date
  = let dat = mkHeadUpData (p{ stack = zf}) in
    unify dat (p { stack = zf :<+>: UnificationProblem (today store) s t : fs })
move p@Process { stack = (zf :< f) :<+>: fs }
  = move (p { stack = zf :<+>: (f : fs) })

debug :: (Show (t Frame), Traversable t, Collapse t, Display0 s)
      => MachineStep -> Doc Annotations -> Process log s t -> Bool
debug step str p | step `elem` tracing p = -- dmesg (show step ++ ": " ++ show p) $
  let (fs', store', env', a') = unsafeEvalDisplay initDEnv $ displayProcess' p
      p' = hang 2 (flush "") $ vcat $ [collapse fs', store', env', a']
      step' = keyword (pretty step)
      msg = renderWith (renderOptions (options p)) $ vcat [mempty, step' <+> str, p']
  in dmesg msg False
debug step _ p = False
