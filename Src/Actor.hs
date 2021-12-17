module Actor where


import Control.Monad.Reader
import Control.Monad.Writer
import Control.Applicative

import qualified Data.Map as Map

import Bwd
import Display
import Hide
import Term
import Thin

import Debug.Trace

dmesg = trace

-- TODO:
--  A zipper for process trees

type Channel = String
type ActorVar = String -- Stands for a term
type JudgementForm = String
type Gripe = String

data Actor
 = Actor :|: Actor
 | Spawn JudgementForm Channel Actor
 | Send Channel (CdB (Tm ActorVar)) Actor
 | Recv Channel ActorVar Actor
 | FreshMeta ActorVar Actor
 | Under ActorVar Actor
 | Match (CdB (Tm ActorVar)) [(Pat, Actor)]
 -- This is going to bite us when it comes to dependent types
 | Constrain (CdB (Tm ActorVar)) (CdB (Tm ActorVar))
 | Extend JudgementForm ActorVar (Channel, Actor) Actor
 | Fail Gripe
 | Win
 deriving Show

check :: (JudgementForm, (Channel, Actor))
check = ("check", ("p", Recv "p" "ty" $
                        Recv "p" "tm" $
                        Match ("tm" $: sbst0 0)
        [ ("Lam" #? [BP (Hide "x") (MP "body" (ones 1))]
          ,FreshMeta "S" $
           FreshMeta "T" $
            let ty = Constrain ("ty" $: sbst0 0) ("Arr" #%+ [("S" $: sbst0 0), ("T" $: sbst0 0)])
                body = Under "y" $
                       Extend "synth" "y" ("r", Send "r" ("S" $: sbst0 0) Win) $
                       Spawn "check" "q" $
                       Send "q" ("T" $: sbst0 0) $
                       Send "q" ("body" $: (sbstT (sbst0 0) ((Hide "x" :=) $^ ("y" $: sbst0 0)))) Win
            in  ty :|: body)
        , ("Emb" #? [MP "e" (ones 0)]
          ,Spawn "synth" "q" $
           Send "q" ("e" $: sbst0 0) $
           Recv "q" "S" $
           Constrain ("S" $: sbst0 0) ("ty" $: sbst0 0))
        ]))

synth :: (JudgementForm, (Channel, Actor))
synth =
  ("synth", ("p", Recv "p" "tm" $ Match ("tm" $: sbst0 0)
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
  = LeftBranch Hole (Process [])
  | RightBranch (Process []) Hole
  | Spawnee (Hole, Channel) (Channel, Process [])
  | Spawner (Process [], Channel) (Channel, Hole)
  | Sent Channel Term
  | Defn ActorVar Term
  | Binding String
  -- Left: which dependencies are permitted
  -- Right: what solution we already have
  | DeclMeta Meta (Either Th Term)
  | UnificationProblem Term Term
  deriving Show

type Process t
  = (t Frame -- Stack frames ahead of or behind us
    ,Root    -- Name supply
    ,Int     -- Number of things in scope
    ,Actor   -- The thing we are
    )

-- Hardwired judgement forms that we know how to do
judgementForms :: [(JudgementForm, (Channel, Actor))]
judgementForms = [synth, check]

processTest :: Process Bwd
processTest
  = (B0, initRoot, 0, Spawn "check" "p" $
                      Send "p" ("Arr" #%+ [nat, nat]) $
                      Send "p" ("Lam" #%+ ["x" \\ ("Emb" #%+ [var 0 1])]) $
                      Win)
 where
  nat = ("Nat", 0) #% []

-- run an actor
exec :: Process Bwd -> Process []
exec (zf, _, _, a)
 | dmesg ("\nexec\n  " ++ show zf ++ "\n  " ++ show a) False = undefined
exec (zf, root, scope, a :|: b) = exec (zf :< LeftBranch Hole ([], rroot, scope, b), lroot, scope, a)
 where
  (lroot, rroot) = splitRoot root ""
exec (zf, root, scope, Spawn j p actor)
 | Just (q, spawnedActor) <- lookup j judgementForms
  = exec (zf :< Spawnee (Hole, q) (p, ([], newRoot, scope, actor)), subRoot, scope, spawnedActor)
 where
  (subRoot, newRoot) = splitRoot root j
exec (zf, root, scope, Send p tm actor)
  | Just term <- mangleActors zf tm
  = send p (tm, term) (zf :<+>: [], newRoot, scope, actor)
 where
  (subRoot, newRoot) = splitRoot root ""
exec (zf, root, scope, Recv p x actor) = recv p x (zf :<+>: [], root, scope, actor)
exec (zf, root, scope, m@(Match s ((pat, a):cs)))
  | Just term <- mangleActors zf s
  = match zf [(pat, term)]
 where
  match :: Bwd Frame -> [(Pat, Term)] -> Process []
  match zf [] = exec (zf, root, scope, a)
  match zf' ((MP x ph, (t, th)):xs)
    = let g = bigEnd th - bigEnd ph
      in  case thicken (ones g <> ph) th of
            Just ps -> match (zf' :< Defn x (t, ps)) xs
            Nothing -> exec (zf, root, scope, Match s cs)
  match zf' ((p, tm):xs) = case (p, expand tm) of
    (_, (_ :$: _)) -> move (zf :<+>: [], root, scope, m)
    (VP i, VX j _) | i == j -> match zf' xs
    (AP a, AX b _) | a == b -> match zf' xs
    (PP p q, s :%: t) -> match zf' ((p,s):(q,t):xs)
    (BP _ p, _ :.: t) -> match zf' ((p,t):xs)
    _ -> exec (zf, root, scope, Match s cs)
exec (zf, root, scope, FreshMeta x a) = exec (zf :< DeclMeta xm Nothing :< Defn x xt, root', scope, a)
  where
  (xm, root') = meta root x
  xt = xm $: sbstI scope
exec (zf, root, scope, Constrain s t)
 | Just s' <- mangleActors zf s,
   Just t' <- mangleActors zf t = unify (zf :<+>: [UnificationProblem s' t'], root, scope, Win)

exec (zf, root, scope, actor) = move (zf :<+>: [], root, scope, actor)

mangleActors :: Bwd Frame -> CdB (Tm String) -> Maybe Term
mangleActors zf tm = go tm
 where
  go :: CdB (Tm String) -> Maybe Term
  go tm = case expand tm of
            m :$: sbst -> (//^) <$> lookupVar zf m <*> goSbst zf sbst
            VX i j -> pure $ var i j
            AX s i -> pure $ atom s i
            a :%: b -> (%) <$> go a <*> go b
            x :.: t -> (x \\) <$> mangleActors (zf :< Binding x) t

  goSbst :: Bwd Frame -> CdB (Sbst String) -> Maybe Subst
  goSbst _ (S0 :^^ 0, th) = pure (S0 :^^ 0, th)
  goSbst zf (ST rp :^^ 0, th) = splirp (rp, th) $ \s (x := tm, ph) -> do
    s <- goSbst zf s
    tm <- mangleActors zf (tm, ph)
    pure $ sbstT s ((x :=) $^ tm)
  goSbst (zf :< Binding _) (sbst :^^ w, th)
    | (ph, True) <- thun th = do
        sbst <- goSbst zf (sbst :^^ (w - 1), ph)
        pure $ sbstW sbst (ones 1)

  lookupVar :: Bwd Frame -> String -> Maybe Term
  lookupVar B0 _ = Nothing
  lookupVar (zf :< Defn x t) y | x == y = Just t
  lookupVar (zf :< Binding _) y = weak <$> lookupVar zf y
  lookupVar (zf :< Spawnee _ _) y = Nothing
  lookupVar (zf :< _) y = lookupVar zf y

actorVarsMangler :: Int -> Int -> Mangler (Reader (Bwd Frame))
actorVarsMangler xi ga = Mangler
  { mangGlo = xi
  , mangLoc = ga
  , mangV   = pure (V, none xi -? True)
  , mangB   = actorVarsMangler xi (ga + 1)
  , mangM   = error ""
  , mangSelFrom = \ ph -> actorVarsMangler xi (weeEnd ph)
  }

unify :: Process Cursor -> Process []
unify (zf :<+>: UnificationProblem s t : fs, root, scope, a) = case (expand s, expand t) of
  (VX i _, VX i' _)     | i  == i'  -> unify (zf :<+>: fs, root, scope, a)
  (AX at _, AX at' _)   | at == at' -> unify (zf :<+>: fs, root, scope, a)
  (p :%: q, p' :%: q') -> unify (zf :<+>: UnificationProblem p p' : UnificationProblem q q' : fs, root, scope, a)
  (x :.: p, x' :.: p') -> unify (zf :<+>: UnificationProblem p p' : fs, root, scope, a)
  (m :$: sg, m' :$: sg') | m == m' -> _ -- STILL LEFT TO DO
  (m :$: sg, _) -> solveMeta [] m sg t (zf :<+>: fs, root, scope, a)
  (_, m :$: sg) -> solveMeta [] m sg s (zf :<+>: fs, root, scope, a)
  (_, _) -> move (zf :<+>: UnificationProblem s t : fs, root, scope, Fail "Unification failure")
unify p = move p

solveMeta :: [Meta] -- The meta's (ms) that we're moving
          -> Meta   -- The meta (m) we're solving
          -> Subst  -- The substitution (sg) which acts on m
          -> Term   -- The term (t) that must be equal to m :$ sg and depends on ms
          -> Process Cursor
          -> Process []
solveMeta ms m sg t (zf :<+>: fs, root, scope, a) = case zf of
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

send :: Channel -> (CdB (Tm String), Term) -> Process Cursor -> Process []
send ch (tm, term) (zfs@(zf :<+>: fs), _, _, a)
 | dmesg ("\nsend " ++ show ch ++ " " ++ display' (frnaming zf) term ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
send p (tm, term) (B0 :<+>: fs, root, scope, actor) = move (B0 <>< fs :<+>: [], root, scope, Send p tm actor)
send p (tm, term) ((zf :< Spawner ((cfs, croot, cscope, childActor), q) (r, Hole)) :<+>: fs, root, scope, actor)
 | r == p = exec (zf :< Spawnee (Hole, q) (r, (fs, root, scope, actor)) :< Sent q term <>< cfs, croot, cscope, childActor)
send p (tm, term) (zf'@(zf :< Spawnee (Hole, q) (r, (pfs, proot, pscope, parentActor))) :<+>: fs, root, scope, actor)
 | p == q = exec (zf :< Spawnee (Hole, q) (r, (Sent r term : pfs, proot, pscope, parentActor)) <>< fs, root, scope, actor)
 | otherwise = move (zf' <>< fs :<+>: [], root, scope, Send p tm actor)
send p (tm, term) ((zf :< f) :<+>: fs, root, scope, actor) = send p (tm, term) (zf :<+>: (f:fs), root, scope, actor)

recv :: Channel -> ActorVar -> Process Cursor -> Process []
recv ch v (zfs, _, _, a)
 | dmesg ("\nrecv " ++ show ch ++ " " ++ show v ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
recv p x (B0 :<+>: fs, root, scope, actor) = move (B0 <>< fs :<+>: [], root, scope, Recv p x actor)
recv p x (zf :< Sent q y :<+>: fs, root, scope, actor)
 | p == q = exec (zf :< Defn x y <>< fs, root, scope, actor)
recv p x (zf'@(zf :< Spawnee (Hole, q) (r, process)) :<+>: fs, root, scope, actor)
 = move (zf' <>< fs :<+>: [], root, scope, Recv p x actor)
recv p x (zf :< f :<+>: fs, root, scope, actor) = recv p x (zf :<+>: (f:fs), root, scope, actor)

-- find the next thing to run
move :: Process Cursor -> Process []
move (zfs, _, _, a)
 | dmesg ("\nmove\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
move (B0 :<+>: fs, root, scope, actor) = (fs, root, scope, actor)
move ((zf :< LeftBranch Hole (rfs, rroot, rscope, ractor)) :<+>: fs, root, scope, actor)
  = exec (zf :< RightBranch (fs, root, scope, actor) Hole <>< rfs, rroot, rscope, ractor)
move ((zf :< Spawnee (Hole, p) (q, (sfs, sroot, sscope, parentActor))) :<+>: fs, root, scope, childActor)
  = exec (zf :< Spawner ((fs, root, scope, childActor), p) (q, Hole) <>< sfs, sroot, sscope, parentActor)
move ((zf :< f) :<+>: fs, root, scope, actor) = move (zf :<+>: (f:fs), root, scope, actor)

frnaming :: Bwd Frame -> Naming
frnaming zf = (zv, ones (length zv), zv)
 where
  zv = flip foldMap zf $ \case
    Binding x -> B0 :< x
    _ -> B0
