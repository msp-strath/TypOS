{-# LANGUAGE FlexibleInstances, OverloadedStrings #-}

module Actor where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Applicative

import qualified Data.Map as Map
import Data.String (IsString(..))

import Bwd
import Display
import Hide
import Term
import Thin

import Debug.Trace

dmesg = trace

-- TODO:
--  A zipper for process trees

type Store = Map.Map Meta Term
type Channel = String
data ActorVar = ActorVar String -- Stands for a term
  deriving (Eq)
instance Show ActorVar where
  show (ActorVar str) = str

instance IsString ActorVar where
  fromString = ActorVar

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

instance Display Actor where
  display na = \case
    a :|: b -> pdisplay na a ++ " :|: " ++ pdisplay na b
    Spawn jd ch a -> unwords ["Spawn", jd, show ch, pdisplay na a]
    Send ch tm a -> unwords ["Send", show ch, pdisplay na tm, pdisplay na a]
    Recv ch av a -> unwords ["Recv", show ch, show av, pdisplay na a]
    FreshMeta av a -> unwords ["FreshMeta", show av, pdisplay na a]
    Under av a -> unwords ["Under", show av, pdisplay na a]
    Match t pts -> unwords ["Match", pdisplay na t, collapse (display na <$> pts)]
    Constrain s t -> unwords ["Constrain", pdisplay na s, pdisplay na t]
    Extend jd av (ch, a) b -> unwords ["Extend", jd, show av, show ch, pdisplay na a, pdisplay na b]
    Fail gr -> unwords ["Fail", gr]
    Win -> "Win"

instance Display (Pat, Actor) where
  display na (p, a) = display na p ++ " -> " ++ display na a

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
  = LeftBranch Hole (Process () [])
  | RightBranch (Process () []) Hole
  | Spawnee (Hole, Channel) (Channel, Process () [])
  | Spawner (Process () [], Channel) (Channel, Hole)
  | Sent Channel Term
  | Defn ActorVar Term
  | Binding String
  | UnificationProblem Term Term
  deriving (Show)

instance Display Frame where
  display na = \case
    LeftBranch Hole p -> "<> | " ++ display na p
    RightBranch p Hole -> display na p ++ " | <>"
    Spawnee (Hole, lch) (rch, p) -> "<> @ " ++ show lch ++ " | " ++ show rch ++ " @ " ++ display na p
    Spawner (p, lch) (rch, Hole) -> display na p ++ " @ " ++ show lch ++ " | " ++ show rch ++ " @ <>"
    Sent ch t -> "!" ++ ch ++ ". " ++ display na t
    Defn v t -> show v ++ " := " ++ display na t
    Binding x -> "\\" ++ x ++ ". "
    UnificationProblem s t -> display na s ++ " ~? " ++ display na t

instance (Traversable t, Collapse t, Display s) => Display (Process s t) where
  display na (fs, rt, n, store, a) =
     let (fs', na') = runState (traverse go fs) na
         store'     = display na store
         a'         = display na' a
     in unlines $ map ("  " ++) [ collapse fs', store', a']

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

{-
data Process s t
  = Process
  { stack  :: t Frame -- Stack frames ahead of or behind us
  , supply :: Root    -- Name supply
  , gamma  :: Int     -- Number of things in scope
  , store  :: s       -- Definitions we know for metas (or not)
  , actor  :: Actor   -- The thing we are
  }
-}

type Process s t
  =
  ( t Frame -- Stack frames ahead of or behind us
  , Root    -- Name supply
  , Int     -- Number of things in scope
  , s       -- Definitions we know for metas (or not)
  , Actor   -- The thing we are
  )

stack :: Process s t -> t Frame
stack (fs, _, _, _, _) = fs

-- Hardwired judgement forms that we know how to do
judgementForms :: [(JudgementForm, (Channel, Actor))]
judgementForms = [synth, check]

processTest :: Process Store Bwd
processTest
  = (B0, initRoot, 0, Map.empty,) $
      Spawn "check" "p" $
      Send "p" ("Arr" #%+ [nat, bool]) $
      Send "p" ("Lam" #%+ ["x" \\ ("Emb" #%+ [var 0 1])]) $
      Win
 where
  nat = ("Nat", 0) #% []
  bool = ("Bool", 0) #% []

debug :: (Traversable t, Collapse t, Display s)
      => String -> Process s t -> Bool
debug str p =
  dmesg ("\n" ++ str ++ "\n" ++ display initNaming p) False

-- run an actor
exec :: Process Store Bwd -> Process Store []
exec (zf, _, _, store, a)
  | dmesg ("\nexec\n  " ++ show zf ++ "\n  " ++ show store ++ "\n  " ++ show a) False = undefined
exec p | debug "exec" p = undefined
exec (zf, root, scope, store, a :|: b) = exec (zf :< LeftBranch Hole ([], rroot, scope, (), b), lroot, scope, store, a)
 where
  (lroot, rroot) = splitRoot root ""
exec (zf, root, scope, store, Spawn j p actor)
 | Just (q, spawnedActor) <- lookup j judgementForms
  = exec (zf :< Spawnee (Hole, q) (p, ([], newRoot, scope, (), actor)), subRoot, scope, store, spawnedActor)
 where
  (subRoot, newRoot) = splitRoot root j
exec (zf, root, scope, store, Send p tm actor)
  | Just term <- mangleActors zf tm
  = send p (tm, term) (zf :<+>: [], newRoot, scope, store, actor)
 where
  (subRoot, newRoot) = splitRoot root ""
exec (zf, root, scope, store, Recv p x actor) = recv p x (zf :<+>: [], root, scope, store, actor)
exec (zf, root, scope, store, m@(Match s ((pat, a):cs)))
  | Just term <- mangleActors zf s
  = match zf [(pat, term)]
 where
  match :: Bwd Frame -> [(Pat, Term)] -> Process Store []
  match zf [] = exec (zf, root, scope, store, a)
  match zf' ((MP x ph, (t, th)):xs)
    = let g = bigEnd th - bigEnd ph
      in  case thicken (ones g <> ph) th of
            Just ps -> match (zf' :< Defn (ActorVar x) (t, ps)) xs
            -- bug: t may not depend on disallowed things until definitions are expanded
            Nothing -> exec (zf, root, scope, store, Match s cs)
  match zf' ((p, tm):xs) = case (p, expand (headUp store tm)) of
    (_, (_ :$: _)) -> move (zf :<+>: [], root, scope, store, m)
    (VP i, VX j _) | i == j -> match zf' xs
    (AP a, AX b _) | a == b -> match zf' xs
    (PP p q, s :%: t) -> match zf' ((p,s):(q,t):xs)
    (BP _ p, _ :.: t) -> match zf' ((p,t):xs)
    _ -> exec (zf, root, scope, store, Match s cs)
exec (zf, root, scope, store, FreshMeta av@(ActorVar x) a) = exec (zf :< Defn av xt, root', scope, store, a)
  where
  (xm, root') = meta root x
  xt = xm $: sbstI scope
exec (zf, root, scope, store, Constrain s t)
 | Just s' <- mangleActors zf s,
   Just t' <- mangleActors zf t = unify (zf :<+>: [UnificationProblem s' t'], root, scope, store, Win)

exec (zf, root, scope, store, actor) = move (zf :<+>: [], root, scope, store, actor)

mangleActors :: Bwd Frame -> CdB (Tm ActorVar) -> Maybe Term
mangleActors zf tm = go tm
 where
  go :: CdB (Tm ActorVar) -> Maybe Term
  go tm = case expand tm of
            m :$: sbst -> (//^) <$> lookupVar zf m <*> goSbst zf sbst
            VX i j -> pure $ var i j
            AX s i -> pure $ atom s i
            a :%: b -> (%) <$> go a <*> go b
            x :.: t -> (x \\) <$> mangleActors (zf :< Binding x) t

  goSbst :: Bwd Frame -> CdB (Sbst ActorVar) -> Maybe Subst
  goSbst _ (S0 :^^ 0, th) = pure (S0 :^^ 0, th)
  goSbst zf (ST rp :^^ 0, th) = splirp (rp, th) $ \s (x := tm, ph) -> do
    s <- goSbst zf s
    tm <- mangleActors zf (tm, ph)
    pure $ sbstT s ((x :=) $^ tm)
  goSbst (zf :< Binding _) (sbst :^^ w, th)
    | (ph, True) <- thun th = do
        sbst <- goSbst zf (sbst :^^ (w - 1), ph)
        pure $ sbstW sbst (ones 1)

  lookupVar :: Bwd Frame -> ActorVar -> Maybe Term
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

unify :: Process Store Cursor -> Process Store []
unify p | debug "unify" p = undefined
--unify (zf :<+>: up@(UnificationProblem s t) : fs, _, _, store, a)
-- | dmesg ("\nunify\n  " ++ show up ++ "\n  " ++ show store ++ "\n  " ++ show a) False = undefined
unify (zf :<+>: UnificationProblem s t : fs, root, scope, store, a) = case (expand (headUp store s), expand (headUp store t)) of
  (s, t) | s == t      -> unify (zf :<+>: fs, root, scope, store, a)
  (p :%: q, p' :%: q') -> unify (zf :<+>: UnificationProblem p p' : UnificationProblem q q' : fs, root, scope, store, a)
  (x :.: p, x' :.: p') -> unify (zf :<+>: UnificationProblem p p' : fs, root, scope, store, a)
  (m :$: sg, _) | Just p <- solveMeta m sg t (zf :<+>: fs, root, scope, store, a) -> unify p
  (_, m :$: sg) | Just p <- solveMeta m sg s (zf :<+>: fs, root, scope, store, a) -> unify p
  (_, _) -> unify (zf :< UnificationProblem s t :<+>: fs, root, scope, store, a)
unify p = move p

solveMeta :: Meta   -- The meta (m) we're solving
          -> Subst  -- The substitution (sg) which acts on m
          -> Term   -- The term (t) that must be equal to m :$ sg and depends on ms
          -> Process Store Cursor
          -> Maybe (Process Store Cursor)
solveMeta m (S0 :^^ _, ph) (tm, th) (zf :<+>: fs, root, scope, store, a) = do
  ps <- thicken ph th
  -- FIXME: do a deep occurs check here to avoid the bug from match 
  return (zf :<+>: fs, root, scope, (Map.insert m (tm, ps) store), a)
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

send :: Channel -> (CdB (Tm ActorVar), Term) -> Process Store Cursor -> Process Store []
send ch (tm, term) p
 | debug ("send "  ++ show ch ++ " " ++ display (frnaming (stack p)) term) p
 = undefined
-- send ch (tm, term) (zfs@(zf :<+>: fs), _, _, _, a)
--  | dmesg ("\nsend " ++ show ch ++ " " ++ display (frnaming zf) term ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
send p (tm, term) (B0 :<+>: fs, root, scope, store, actor) = move (B0 <>< fs :<+>: [], root, scope, store, Send p tm actor)
send p (tm, term) ((zf :< Spawner ((cfs, croot, cscope, (), childActor), q) (r, Hole)) :<+>: fs, root, scope, store, actor)
 | r == p = exec (zf :< Spawnee (Hole, q) (r, (fs, root, scope, (), actor)) :< Sent q term <>< cfs, croot, cscope, store, childActor)
send p (tm, term) (zf'@(zf :< Spawnee (Hole, q) (r, (pfs, proot, pscope, (), parentActor))) :<+>: fs, root, scope, store, actor)
 | p == q = exec (zf :< Spawnee (Hole, q) (r, (Sent r term : pfs, proot, pscope, (), parentActor)) <>< fs, root, scope, store, actor)
 | otherwise = move (zf' <>< fs :<+>: [], root, scope, store, Send p tm actor)
send p (tm, term) ((zf :< f) :<+>: fs, root, scope, store, actor) = send p (tm, term) (zf :<+>: (f:fs), root, scope, store, actor)

recv :: Channel -> ActorVar -> Process Store Cursor -> Process Store []
recv ch v p | debug ("recv " ++ show ch ++ " " ++ show v) p = undefined
-- recv ch v (zfs, _, _, _, a)
 -- | dmesg ("\nrecv " ++ show ch ++ " " ++ show v ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
recv p x (B0 :<+>: fs, root, scope, store, actor) = move (B0 <>< fs :<+>: [], root, scope, store, Recv p x actor)
recv p x (zf :< Sent q y :<+>: fs, root, scope, store, actor)
 | p == q = exec (zf :< Defn x y <>< fs, root, scope, store, actor)
recv p x (zf'@(zf :< Spawnee (Hole, q) (r, process)) :<+>: fs, root, scope, store, actor)
 = move (zf' <>< fs :<+>: [], root, scope, store, Recv p x actor)
recv p x (zf :< f :<+>: fs, root, scope, store, actor) = recv p x (zf :<+>: (f:fs), root, scope, store, actor)

-- find the next thing to run
move :: Process Store Cursor -> Process Store []
move p | debug "move" p = undefined
-- move (zfs, _, _, store, a)
-- | dmesg ("\nmove\n  " ++ show zfs ++ "\n  " ++ show store ++ "\n  " ++ show a) False = undefined
move (B0 :<+>: fs, root, scope, store, actor) = (fs, root, scope, store, actor)
move ((zf :< LeftBranch Hole (rfs, rroot, rscope, (), ractor)) :<+>: fs, root, scope, store, actor)
  = exec (zf :< RightBranch (fs, root, scope, (), actor) Hole <>< rfs, rroot, rscope, store, ractor)
move ((zf :< Spawnee (Hole, p) (q, (sfs, sroot, sscope, (), parentActor))) :<+>: fs, root, scope, store, childActor)
  = exec (zf :< Spawner ((fs, root, scope, (), childActor), p) (q, Hole) <>< sfs, sroot, sscope, store, parentActor)
move ((zf :< f) :<+>: fs, root, scope, store, actor) = move (zf :<+>: (f:fs), root, scope, store, actor)

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
