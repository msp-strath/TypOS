module Actor where

import Control.Monad.Reader

import Bwd
import Hide
import Term
import Thin

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
                         Recv "q" "ty" $
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
exec (zf, root, scope, a :|: b) = exec (zf :< LeftBranch Hole ([], rroot, scope, b), lroot, scope, a)
 where
  (lroot, rroot) = splitRoot root ""
exec (zf, root, scope, Spawn j p actor)
 | Just (q, spawnedActor) <- lookup j judgementForms
  = exec (zf :< Spawnee (Hole, q) (p, ([], newRoot, scope, actor)), subRoot, scope, spawnedActor)
 where
  (subRoot, newRoot) = splitRoot root j
exec (zf, root, scope, Send p tm actor) = send p (tm, lookupActorVars subRoot scope zf tm) (zf :<+>: [], newRoot, scope, actor)
 where
  (subRoot, newRoot) = splitRoot root ""
exec (zf, root, scope, Recv p x actor) = recv p x (zf :<+>: [], root, scope, actor)
exec (zf, root, scope, actor) = move (zf :<+>: [], root, scope, actor)

-- very very shit temporary hack because we haven't implemented `recv` yet
lookupActorVars :: Root -> Int -> Bwd Frame -> CdB (Tm String) -> Term
lookupActorVars (meta, _) scope zf tm = (notSoShitMeta <$>) $^ tm
 where
  notSoShitMeta s = Meta (meta <>> [(s, 0)])

actorVarsMangler :: Int -> Int -> Mangler (Reader (Bwd Frame))
actorVarsMangler xi ga = Mangler
  { mangGlo = xi
  , mangLoc = ga
  , mangV   = pure (V, none xi -? True)
  , mangB   = actorVarsMangler xi (ga + 1)
  , mangM   = error ""
  , mangSelFrom = \ ph -> actorVarsMangler xi (weeEnd ph)
  }

send :: Channel -> (CdB (Tm String), Term) -> Process Cursor -> Process []
send p (tm, term) (B0 :<+>: fs, root, scope, actor) = move (B0 <>< fs :<+>: [], root, scope, Send p tm actor)
send p (tm, term) ((zf :< Spawner ((cfs, croot, cscope, childActor), q) (r, Hole)) :<+>: fs, root, scope, actor)
 | r == p = exec (zf :< Spawnee (Hole, q) (r, (fs, root, scope, actor)) :< Sent q term <>< cfs, croot, cscope, childActor)
send p (tm, term) (zf'@(zf :< Spawnee (Hole, q) (r, (pfs, proot, pscope, parentActor))) :<+>: fs, root, scope, actor)
 | p == q = exec (zf :< Spawnee (Hole, q) (r, (Sent r term : pfs, proot, pscope, parentActor)) <>< fs, root, scope, actor)
 | otherwise = move (zf' <>< fs :<+>: [], root, scope, Send p tm actor)
send p (tm, term) ((zf :< f) :<+>: fs, root, scope, actor) = send p (tm, term) (zf :<+>: (f:fs), root, scope, actor)

recv :: Channel -> ActorVar -> Process Cursor -> Process []
recv p x (B0 :<+>: fs, root, scope, actor) = move (B0 <>< fs :<+>: [], root, scope, Recv p x actor)
recv p x (zf :< Sent q y :<+>: fs, root, scope, actor)
 | p == q = exec (zf :< Defn x y <>< fs, root, scope, actor)
recv p x (zf'@(zf :< Spawnee (Hole, q) (r, process)) :<+>: fs, root, scope, actor)
 = move (zf' <>< fs :<+>: [], root, scope, Recv p x actor)
recv p x (zf :< f :<+>: fs, root, scope, actor) = recv p x (zf :<+>: (f:fs), root, scope, actor)

-- find the next thing to run
move :: Process Cursor -> Process []
move (B0 :<+>: fs, root, scope, actor) = (fs, root, scope, actor)
move ((zf :< LeftBranch Hole (rfs, rroot, rscope, ractor)) :<+>: fs, root, scope, actor)
  = exec (zf :< RightBranch (fs, root, scope, actor) Hole <>< rfs, rroot, rscope, ractor)
move ((zf :< Spawnee (Hole, p) (q, (sfs, sroot, sscope, parentActor))) :<+>: fs, root, scope, childActor)
  = exec (zf :< Spawner ((fs, root, scope, childActor), p) (q, Hole) <>< sfs, sroot, sscope, parentActor)
move ((zf :< f) :<+>: fs, root, scope, actor) = move (zf :<+>: (f:fs), root, scope, actor)
