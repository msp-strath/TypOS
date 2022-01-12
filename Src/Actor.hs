{-# LANGUAGE FlexibleInstances, OverloadedStrings, StandaloneDeriving #-}

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
  display na Process{..} =
     let (fs', na') = runState (traverse go stack) na
         store'     = display na store
         a'         = display na' actor
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
    go (k, t) = "?" ++ show k ++ " := " ++ display (fromScope (Thin.scope t)) t

data Process s t
  = Process
  { stack :: t Frame -- Stack frames ahead of or behind us
  , root  :: Root    -- Name supply
  , scope :: Int     -- Number of things in scope
  , store :: s       -- Definitions we know for metas (or not)
  , actor :: Actor   -- The thing we are
  }

deriving instance (Show s, Show (t Frame)) => Show (Process s t)

-- Hardwired judgement forms that we know how to do
judgementForms :: [(JudgementForm, (Channel, Actor))]
judgementForms = [synth, check]

processTest :: Process Store Bwd
processTest
  = Process B0 initRoot 0 Map.empty $
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
exec (Process zf _ _ store a)
  | dmesg ("\nexec\n  " ++ show zf ++ "\n  " ++ show store ++ "\n  " ++ show a) False = undefined
exec p | debug "exec" p = undefined
exec p@Process { actor = a :|: b, ..} =
  let (lroot, rroot) = splitRoot root ""
      rbranch = Process [] rroot scope () b
  in exec (p { stack = stack :< LeftBranch Hole rbranch, root = lroot, actor = a})
exec p@Process { actor = Spawn jd spawnerCh actor, ..}
  | Just (spawnedCh, spawnedActor) <- lookup jd judgementForms
  = let (subRoot, newRoot) = splitRoot root jd
        spawner = Process [] newRoot scope () actor
    in exec (p { stack = stack :< Spawnee (Hole, spawnedCh) (spawnerCh, spawner)
               , root = subRoot
               , actor = spawnedActor })
exec p@Process { actor = Send ch tm a, ..}
  | Just term <- mangleActors stack tm
  = let (subRoot, newRoot) = splitRoot root ""
    in send ch (tm, term) (p { stack = stack :<+>: [], root = newRoot, actor = a })
exec p@Process { actor = Recv ch x a, ..}
  = recv ch x (p { stack = stack :<+>: [], actor = a })
exec p@Process { actor = m@(Match s ((pat, a):cs)), ..}
  | Just term <- mangleActors stack s
  = match stack [(pat, term)]
 where
  match :: Bwd Frame -> [(Pat, Term)] -> Process Store []
  match stack' [] = exec (p { stack = stack', actor = a })
  match stack' ((MP x ph, (t, th)):xs)
    = let g = bigEnd th - bigEnd ph
      in  case thicken (ones g <> ph) th of
            Just ps -> match (stack' :< Defn (ActorVar x) (t, ps)) xs
            -- bug: t may not depend on disallowed things until definitions are expanded
            Nothing -> exec (p { actor = Match s cs })
  match stack' ((pat, tm):xs) = case (pat, expand (headUp store tm)) of
    (_, (_ :$: _)) -> move (p { stack = stack :<+>: [], actor = m })
    (VP i, VX j _) | i == j -> match stack' xs
    (AP a, AX b _) | a == b -> match stack' xs
    (PP p q, s :%: t) -> match stack' ((p,s):(q,t):xs)
    (BP _ p, _ :.: t) -> match stack' ((p,t):xs)
    _ -> exec (p { actor = Match s cs })
exec p@Process { actor = FreshMeta av@(ActorVar x) a, ..} =
  let (xm, root') = meta root x
      xt = xm $: sbstI scope
  in exec (p { stack = stack :< Defn av xt, root = root', actor = a })
exec p@Process { actor = Constrain s t, ..}
 | Just s' <- mangleActors stack s
 , Just t' <- mangleActors stack t
 = unify (p { stack = stack :<+>: [UnificationProblem s' t'], actor = Win })
exec p@Process {..} = move (p { stack = stack :<+>: [] })

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

send :: Channel -> (CdB (Tm ActorVar), Term) -> Process Store Cursor -> Process Store []
send ch (tm, term) p
 | debug ("send "  ++ show ch ++ " " ++ display (frnaming (stack p)) term) p
 = undefined
-- send ch (tm, term) (zfs@(zf :<+>: fs), _, _, _, a)
--  | dmesg ("\nsend " ++ show ch ++ " " ++ display (frnaming zf) term ++ "\n  " ++ show zfs ++ "\n  " ++ show a) False = undefined
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
recv ch x p@Process { stack = zf :< Sent q y :<+>: fs }
  | ch == q = exec (p { stack = zf :< Defn x y <>< fs })
recv ch x p@Process { stack = zf'@(zf :< Spawnee (Hole, q) (r, parentP)) :<+>: fs, ..}
  = move (p { stack = zf' <>< fs :<+>: [], actor = Recv ch x actor })
recv ch x p@Process { stack = zf :< f :<+>: fs }
  = recv ch x (p { stack = zf :<+>: (f:fs) })

-- find the next thing to run
move :: Process Store Cursor -> Process Store []
move p | debug "move" p = undefined
-- move (zfs, _, _, store, a)
-- | dmesg ("\nmove\n  " ++ show zfs ++ "\n  " ++ show store ++ "\n  " ++ show a) False = undefined
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
