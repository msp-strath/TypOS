{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
module Machine.Base where

import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Control.Monad.State

import Actor
import Actor.Display()

import Bwd
import Format
import Options
import Term
import qualified Term.Substitution as Substitution
import Thin
import Concrete.Base
import Data.Bifunctor (Bifunctor(first))

import Machine.Steps
import Machine.Matching
import Debug.Trace (trace)
import Display (unsafeDocDisplay)
import ANSI hiding (withANSI)
import Pretty
import Operator
import Operator.Eval
import Unelaboration.Monad (Naming, UnelabMeta)


newtype Date = Date Int
  deriving (Show, Eq, Ord, Num)

initStore :: StoreF i Date
initStore = Store Map.empty Map.empty 0

tick :: StoreF i Date -> StoreF i Date
tick st@Store{..} = st { today = today + 1 }

declareMeta :: Meta -> i -> StoreF i d -> StoreF i d
declareMeta m i st@Store{..} = st
  { solutions = Map.insert m (i, Nothing) solutions }

updateStore :: Meta -> Term -> StoreF i Date -> StoreF i Date
updateStore m t st@Store{..} = tick $ st
  { solutions = Map.adjust (Just t <$) m solutions }

mkOpTable :: Bwd Frame -> Operator -> Clause
mkOpTable _ (Operator "app") = appClause
mkOpTable _ (Operator "tick") = tickClause
mkOpTable fs op = flip foldMap fs $ \case
  Extended op' cl | op == op' -> cl
  _ -> mempty

defineGuard :: Guard -> Set Guard -> StoreF i d -> StoreF i d
defineGuard g gs = execState (compressGuards g gs)

compressGuards :: Guard -> Set Guard -> State (StoreF i d) (Set Guard)
compressGuards g gs = do
  gs <- foldMap (\ g -> fromMaybe (Set.singleton g) <$> dependencySetCompression g) gs
  modify (\ st -> st { guards = Map.insert g gs (guards st) })
  pure gs

dependencySetCompression :: Guard -> State (StoreF i d) (Maybe (Set Guard))
dependencySetCompression g = do
  gtable <- gets guards
  case Map.lookup g gtable of
    Nothing -> pure Nothing
    Just gs -> Just <$> compressGuards g gs

compareUp :: HeadUpData -> Term -> Term -> Maybe Ordering
compareUp dat s t = case (expand (headUp dat s), expand (headUp dat t)) of
  (VX i _, VX j _) -> pure (compare i j)
  (AX a _, AX b _) -> pure (compare a b)
  (p :%: q, a :%:b) -> do
    c1 <- compareUp dat p a
    case c1 of
      EQ -> compareUp dat q b
      _ -> pure c1
  (x :.: b, y :.: c) -> compareUp dat b c
  (m :$: sg, n :$: sg') | m == n, Just EQ <- comparesUp dat sg sg' -> pure EQ
  (m :$: sg, _) -> Nothing
  (_, m :$: sg) -> Nothing
  (VX{}, _) -> pure LT
  (_, VX{}) -> pure GT
  (AX{}, _) -> pure LT
  (_, AX{}) -> pure GT
  ((:%:){}, _) -> pure LT
  (_, (:%:){}) -> pure GT

comparesUp :: HeadUpData -> Subst -> Subst -> Maybe Ordering
comparesUp dat sg sg' = compareUp dat (toTerm sg) (toTerm sg') where

  toTerm (CdB sg th) = ("Hack", bigEnd th) #% (Substitution.expand sg th <>> [])

class Instantiable t where
  type Instantiated t
  instantiate :: StoreF i d -> t -> Instantiated t
  normalise :: HeadUpData -> t -> Instantiated t

class Instantiable1 t where
  type Instantiated1 t :: * -> *
  instantiate1 :: StoreF i d -> t a -> Instantiated1 t a
  normalise1 :: HeadUpData -> t a -> Instantiated1 t a

instance Instantiable Term where
  type Instantiated Term = Term
  instantiate store term = case expand term of
    VX{}     -> term
    AX{}     -> term
    s :%: t  -> instantiate store s % instantiate store t
    s :-: t  -> contract (instantiate store s :-: instantiate store t)
    x :.: b  -> x \\ instantiate store b
    m :$: sg -> case snd =<< Map.lookup m (solutions store) of
      Nothing -> m $: sg -- TODO: instantiate sg
      Just tm -> instantiate store (tm //^ sg)
    GX g t    -> contract (GX g (instantiate store t))
  normalise dat term = let tnf = headUp dat term in case expand tnf of
    VX{}     -> tnf
    AX{}     -> tnf
    s :%: t  -> normalise dat s % normalise dat t
    s :-: t  -> contract (normalise dat s :-: normalise dat t)
    x :.: b  -> x \\ normalise dat b
    m :$: sg -> m $: sg -- TODO: instantiate sg
    GX g t   -> tnf -- don't compute under guards

followDirectives :: (Show t, Instantiable t, Instantiated t ~ t)
       => HeadUpData -> Format Directive dbg t -> Format () dbg t
followDirectives dat@(HeadUpData _ store _ _ _) = \case
    TermPart Instantiate t -> TermPart () (instantiate store t)
    TermPart Normalise t -> TermPart () (normalise dat t)
    TermPart Raw t -> TermPart () t
    TermPart ShowT t -> StringPart (show t)
    DebugPart dbg  -> DebugPart dbg
    StringPart str -> StringPart str


instance Instantiable t => Instantiable [t] where
  type Instantiated [t] = [Instantiated t]
  instantiate store = map (instantiate store)
  normalise dat = map (normalise dat)

data Hole = Hole deriving Show

data Interface c p = Interface
  { spawnee :: (c, Channel)
  , spawner :: ((Channel, [String]), p)
  , judgeName :: JudgementName
  , judgeProtocol :: AProtocol
  , extractionMode :: ExtractMode
  , traffic :: Bwd Term
  } deriving (Show)

-- Do NOT reorder arguments: derived Ord needs to be this way
data Status
  = New
  | StuckOn Date
  | Dead
  | Done
  deriving (Show, Eq, Ord)

instance Semigroup Status where
  (<>) = min

isDone :: Status -> Bool
isDone Done = True
isDone _ = False

-- unOp 'id       -> Just ("id", [])
-- unOp ['if l r] -> Just ("if", [l,r])
unOp :: CdB (Tm a) -> Maybe (Operator, [CdB (Tm a)])
unOp t = case expand t of
  AX op _ -> pure (Operator op, [])
  CdB (A op) _ :%: args -> do
    ps <- asList pure args
    pure (Operator op, ps)
  _ -> Nothing

toClause :: forall m. (Show m, UnelabMeta m) => Pat -> Bwd (Operator, [Pat]) -> ACTm
         -> Options
         -> (Term' m -> Term' m) -- head normaliser
         -> Env' m
         -> (Term' m, [Term' m]) -- object & parameters
         -> Either (Term' m, [Term' m]) (Term' m)
toClause pobj (ops :< op) rhs opts hnf env targs@(t, args) =
  let msg result = flush $ vcat
        [ hsep ( "Matching"
               : withANSI [SetColour Background Green] (unsafeDocDisplay opts naming t)
               : "-"
               : [let opdoc = pretty (getOperator (fst op)) in case args of
                      [] -> "'" <> opdoc
                      _ -> "['" <> hsep (opdoc : map (unsafeDocDisplay opts naming) args) <> "]"]
               )
        , hsep ( "against"
               : unsafeDocDisplay opts naming pobj
               : flip map (ops <>> [op]) (\ (Operator op, ps) -> "- " <> case ps of
                     [] -> "'" <> pretty op
                     _ -> "['" <> hsep (pretty op : map (unsafeDocDisplay opts naming) ps) <> "]")
               )
               <> " ~> " <> unsafeDocDisplay opts naming rhs
        , result ] in

  let ((t, ts), res) = loop initMatching ops op targs in case res of
    Right mtch | Just val <- mangleActors opts (matchingToEnv mtch env) rhs
      -> whenClause opts (msg (withANSI [SetColour Background Green] "Success!")) $ pure val
      | otherwise -> whenClause opts (msg (withANSI [SetColour Background Red] "Failure")) $ Left (t, ts)
    Left err -> whenClause opts (msg (withANSI [SetColour Background Red] $ "Failure " <> pretty err)) $ Left (t, ts)

  where

  naming :: Naming
  naming = let scp = currentScope env in (scp, ones (length scp), scp)

  whenClause :: Options -> Doc Annotations -> a -> a
  whenClause opts doc a
    | MachineClause `elem` fromMaybe [] (tracingOption opts)
    = trace (renderWith (renderOptions opts) doc) a
    | otherwise = a

  loop :: Matching' m
       -> Bwd (Operator, [Pat])  -- left nested operators
       -> (Operator, [Pat])      -- current operator OP in focus
       -> (Term' m, [Term' m])         -- current term (t -['OP | ts]) already taken apart
       -> ( (Term' m, [Term' m])       -- evaluated (t,ts)
          , Either Failure (Matching' m))
  loop mtch ops (op, ps) (tops, tps) =
    -- match tops against the left-nested (pobj -- ops)
    -- we don't care about the tps yet
    let leftnested = case ops of
          B0 -> match hnf mtch (Problem (localScope env) pobj tops)
          -- leftops + lop to the left of the op currently in focus
          (lops :< (lop, lps)) -> let topsnf = hnf tops in case expand topsnf of
            (ltops :-: loptps) -> let loptpsnf = hnf loptps in case unOp loptpsnf of
              Just (lop', ltps) | lop == lop' ->
                case loop mtch lops (lop, lps) (ltops, ltps) of
                  ((ltops, ltps), res) -> (ltops -% (getOperator lop, ltps), res)
              _ -> (contract (ltops :-: loptpsnf), Left Mismatch) -- Careful: could be a stuck meta
            _ -> (topsnf, Left (whenClause opts (unsafeDocDisplay opts naming topsnf <+> "not an operator application") Mismatch))
    in case leftnested of
      (tops, Left err) -> ((tops, tps), Left err)
      (tops, Right mtch) -> first (tops,) $ matches mtch ps tps

  matches :: Matching' m -> [Pat] -> [Term' m] -> ([Term' m], Either Failure (Matching' m))
  matches mtch [] [] = ([], pure mtch)
  matches mtch (p:ps) (t:ts) = case match hnf mtch (Problem (localScope env) p t) of
    (t, Left err) -> (t:ts, Left err)
    (t, Right mtch) -> first (t:) $ matches mtch ps ts
  matches mtch  _ ts = (ts, Left Mismatch)


appClause :: Clause
appClause = Clause $ \ opts hd env (t, args) ->
  case args of
    [arg] -> case expand (hd t) of
      x :.: b -> Right (b //^ topSbst x arg)
      t -> Left (contract t, args)
    _ -> Left (t, args)

tickClause :: Clause
tickClause = Clause $ \ opts hd env (t, args) -> case args of
  []-> (if not (quiet opts) then trace "Tick" else id) $ Right t
  _ ->  Left (t, args)

data Frame
  = Rules JudgementName AProtocol (Channel, AActor)
  | LeftBranch Hole (Process () Status [])
  | RightBranch (Process () Status []) Hole
  | Spawnee (Interface Hole (Process () Status []))
  | Spawner (Interface (Process () Status []) Hole)
  | Sent Channel (Maybe Guard) ([String], Term)
  | Pushed Stack (DB, ASemanticsDesc, Term)
  | Extended Operator Clause
  | Binding String
  | UnificationProblem Date Term Term
  | Noted
  deriving (Show)

status :: [Frame] -> ACTOR ph -> Date -> Status
status fs a d = minimum (actorStatus a : map frameStatus fs)

  where

  actorStatus :: ACTOR ph -> Status
  actorStatus Win{} = Done
  actorStatus Fail{} = Dead
  actorStatus _ = StuckOn d

  frameStatus :: Frame -> Status
  frameStatus Rules{} = Done
  frameStatus (LeftBranch Hole p) = store p
  frameStatus (RightBranch p Hole) = store p
  frameStatus (Spawnee i) = store (snd $ spawner i)
  frameStatus (Spawner i) = store (fst $ spawnee i)
  frameStatus Sent{} = StuckOn d
  frameStatus Pushed{} = Done
  frameStatus Binding{} = Done
  frameStatus UnificationProblem{} = StuckOn d
  frameStatus Noted = Done

data Process l s t
  = Process
  { options :: Options
  , stack   :: t Frame -- Stack frames ahead of or behind us
  , root    :: Root    -- Name supply
  , env     :: Env     -- Definitions in scope
  , store   :: s       -- Definitions we know for metas (or not)
  , actor   :: AActor  -- The thing we are
  , logs    :: l       -- The shots of the VM's state we have taken
  , geas    :: Guard   -- What we are tasked to discharge
  }

tracing :: Process log s t -> [MachineStep]
tracing = fromMaybe [] . tracingOption . options

instance (Show s, Show (t Frame)) => Show (Process log s t) where
  show (Process opts stack root env store actor _ geas) =
   unwords ["Process ", show opts, show stack, show root, show env, show store, show actor, show geas]
