{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExistentialQuantification #-}

module Machine.Base where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe
import Control.Monad.State

import Actor
import Actor.Display()

import Bwd
import Format
import Options
import Term
import qualified Term.Substitution as Substitution
import Thin
import Concrete.Base (Guard, ExtractMode, ACTOR (..), Operator(..))
import Syntax (SyntaxDesc)
import Data.Bifunctor (Bifunctor(first))

import Machine.Matching
import Debug.Trace (trace)
import Display (unsafeDocDisplayClosed)
import ANSI hiding (withANSI)
import Doc.Render.Terminal
import Doc (hsep, vcat, Doc, Config (..), Orientation(..), (<+>), flush)
import Pretty (pretty)
import Utils()

newtype Date = Date Int
  deriving (Show, Eq, Ord, Num)

-- | i stores extra information, typically a naming
data StoreF i = Store
  { solutions :: Map Meta (i, Maybe Term)
  , guards :: Map Guard (Set Guard) -- key is conjunction of values; acyclic!
  , today :: Date
  } deriving (Show)

initStore :: StoreF i
initStore = Store Map.empty Map.empty 0

tick :: StoreF i -> StoreF i
tick st@Store{..} = st { today = today + 1 }

declareMeta :: Meta -> i -> StoreF i -> StoreF i
declareMeta m i st@Store{..} = st
  { solutions = Map.insert m (i, Nothing) solutions }

updateStore :: Meta -> Term -> StoreF i -> StoreF i
updateStore m t st@Store{..} = tick $ st
  { solutions = Map.adjust (Just t <$) m solutions }

defineGuard :: Guard -> Set Guard -> StoreF i -> StoreF i
defineGuard g gs = execState (compressGuards g gs)

compressGuards :: Guard -> Set Guard -> State (StoreF i) (Set Guard)
compressGuards g gs = do
  gs <- foldMap (\ g -> fromMaybe (Set.singleton g) <$> dependencySetCompression g) gs
  modify (\ st -> st { guards = Map.insert g gs (guards st) })
  pure gs

dependencySetCompression :: Guard -> State (StoreF i) (Maybe (Set Guard))
dependencySetCompression g = do
  gtable <- gets guards
  case Map.lookup g gtable of
    Nothing -> pure Nothing
    Just gs -> Just <$> compressGuards g gs

dependencySet :: StoreF i -> Guard -> Set Guard
dependencySet st@Store{..} g = case Map.lookup g guards of
  Nothing -> Set.singleton g
  Just gs -> foldMap (dependencySet st) gs

data HeadUpData = forall i. HeadUpData
  { opTable :: Operator -> Clause
  , metaStore :: StoreF i
  , huOptions :: Options
  , huEnv :: Env
  }

mkOpTable :: Bwd Frame -> Operator -> Clause
mkOpTable _ (Operator "app") = appClause
mkOpTable _ (Operator "when") = whenClause
mkOpTable _ (Operator "tick") = tickClause
mkOpTable fs op = flip foldMap fs $ \case
  Extended op' cl | op == op' -> cl
  _ -> mempty

-- Expanding the term using the information currently available:
-- + meta solutions
-- + operator clauses
headUp :: HeadUpData -> Term -> Term
headUp dat@HeadUpData{..} term = case expand term of
  m :$: sg | Just (_, Just t) <- Map.lookup m (solutions metaStore)
    -> headUp dat (t //^ sg)
  t :-: o -> case expand o of
    AX op i -> operate (Operator op) (t, [])
    o@(CdB (A op) th :%: wargs) ->
      case asList (\ ps -> pure $ operate (Operator op) (t, ps)) wargs of
        Nothing -> contract (t :-: contract o)
        Just t -> t
    o -> contract (t :-: contract o)
  GX g t -> if Set.null (dependencySet metaStore g) then headUp dat t else term
  _ -> term

  where

  operate :: Operator -> (Term, [Term]) -> Term
  operate op tps = case runClause (opTable op) huOptions (headUp dat) huEnv tps of
    Left (t, ps) -> t -% (getOperator op, ps)
    Right t -> headUp dat t


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
  instantiate :: StoreF i -> t -> Instantiated t
  normalise :: HeadUpData -> t -> Instantiated t

class Instantiable1 t where
  type Instantiated1 t :: * -> *
  instantiate1 :: StoreF i -> t a -> Instantiated1 t a
  normalise1 :: HeadUpData -> t a -> Instantiated1 t a

instance Instantiable Term where
  type Instantiated Term = Term
  instantiate store term = case expand term of
    VX{}     -> term
    AX{}     -> term
    s :%: t  -> instantiate store s % instantiate store t
    s :-: t  -> contract (instantiate store s :-: instantiate store t)
    x :.: b  -> x \\ instantiate store b
    m :$: sg -> case join $ fmap snd $ Map.lookup m (solutions store) of
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
followDirectives dat@(HeadUpData _ store _ _) = \case
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
  , judgeName :: JudgementForm
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

toClause :: Pat -> Bwd (Operator, [Pat]) -> ACTm
         -> Options
         -> (Term -> Term) -- head normaliser
         -> Env
         -> (Term, [Term]) -- object & parameters
         -> Either (Term, [Term]) Term
toClause pobj (ops :< op) rhs opts hnf env targs@(t, args) =
  let msg = \ result -> flush $ vcat
        [ hsep ( "Matching"
               : withANSI [SetColour Background Green] (unsafeDocDisplayClosed opts t)
               : "-"
               : [let opdoc = pretty (getOperator (fst op)) in case args of
                      [] -> "'" <> opdoc
                      _ -> "['" <> hsep (opdoc : map (unsafeDocDisplayClosed opts) args) <> "]"]
               )
        , hsep ( "against"
               : unsafeDocDisplayClosed opts pobj
               : flip map (ops <>> [op]) (\ (Operator op, ps) -> "- " <> case ps of
                     [] -> "'" <> pretty op
                     _ -> "['" <> hsep (pretty op : map (unsafeDocDisplayClosed opts) ps) <> "]")
               )
               <> " ~> " <> unsafeDocDisplayClosed opts rhs
        , result ] in
  let ((t, ts), res) = loop env ops op targs in case res of
    Right env | Just val <- mangleActors opts env rhs
      -> whenClause opts (msg (withANSI [SetColour Background Green] "Success!")) $ pure val
      | otherwise -> whenClause opts (msg (withANSI [SetColour Background Red] "Failure")) $ Left (t, ts)
    Left err -> whenClause opts (msg (withANSI [SetColour Background Red] $ "Failure " <> pretty err)) $ Left (t, ts)

  where

  whenClause :: Options -> Doc Annotations -> a -> a
  whenClause opts doc a
    | MachineClause `elem` fromMaybe [] (tracingOption opts)
    = trace (render (colours opts) (Config (termWidth opts) Vertical) doc) a
    | otherwise = a

  loop :: Env
       -> Bwd (Operator, [Pat])  -- left nested operators
       -> (Operator, [Pat])      -- current operator OP in focus
       -> (Term, [Term])         -- current term (t -['OP | ts]) already taken apart
       -> ( (Term, [Term])       -- evaluated (t,ts)
          , Either Failure Env)
  loop env ops (op, ps) (tops, tps) =
    -- match tops against the left-nested (pobj -- ops)
    -- we don't care about the tps yet
    let leftnested = case ops of
          B0 -> match hnf env (Problem (localScope env) pobj tops)
          -- leftops + lop to the left of the op currently in focus
          (lops :< (lop, lps)) -> let topsnf = hnf tops in case expand topsnf of
            (ltops :-: loptps) -> let loptpsnf = hnf loptps in case unOp loptpsnf of
              Just (lop', ltps) | lop == lop' ->
                case loop env lops (lop, lps) (ltops, ltps) of
                  ((ltops, ltps), res) -> (ltops -% (getOperator lop, ltps), res)
              _ -> (contract (ltops :-: loptpsnf), Left Mismatch) -- Careful: could be a stuck meta
            _ -> (topsnf, Left (whenClause opts (unsafeDocDisplayClosed unsafeOptions topsnf <+> "not an operator application") Mismatch))
    in case leftnested of
      (tops, Left err) -> ((tops, tps), Left err)
      (tops, Right env) -> first (tops,) $ matches env ps tps

  matches :: Env -> [Pat] -> [Term] -> ([Term], Either Failure Env)
  matches env [] [] = ([], pure env)
  matches env (p:ps) (t:ts) = case match hnf env (Problem (localScope env) p t) of
    (t, Left err) -> (t:ts, Left err)
    (t, Right env) -> first (t:) $ matches env ps ts
  matches env _ ts = (ts, Left Mismatch)

newtype Clause = Clause { runClause
  :: Options
  -> (Term -> Term) -- head normaliser
  -> Env
  -> (Term, [Term]) -- object & parameters
  -> Either (Term, [Term]) Term }

instance Semigroup Clause where
  (<>) = mappend

instance Monoid Clause where
  mempty = Clause $ \ _ _ _ -> Left
  mappend cl1 cl2 = Clause $ \ opts hd env ops -> case runClause cl2 opts hd env ops of
    Left ops -> runClause cl1 opts hd env ops
    Right t -> Right t

instance Show Clause where
  show _ = "<fun>"

appClause :: Clause
appClause = Clause $ \ opts hd env (t, args) ->
  case args of
    [arg] -> case expand (hd t) of
      x :.: b -> Right (b //^ topSbst x arg)
      t -> Left (contract t, args)
    _ -> Left (t, args)

whenClause :: Clause
whenClause = Clause $ \ opts hd env (t, args) -> case args of
  [arg] -> case expand (hd arg) of
    AX "True" _ -> Right t
    arg -> Left (t, [contract arg])
  _ ->  Left (t, args)

tickClause :: Clause
tickClause = Clause $ \ opts hd env (t, args) -> case args of
  []-> (if not (quiet opts) then trace "Tick" else id) $ Right t
  _ ->  Left (t, args)

data Frame
  = Rules JudgementForm AProtocol (Channel, AActor)
  | LeftBranch Hole (Process () Status [])
  | RightBranch (Process () Status []) Hole
  | Spawnee (Interface Hole (Process () Status []))
  | Spawner (Interface (Process () Status []) Hole)
  | Sent Channel ([String], Term)
  | Pushed Stack (DB, SyntaxDesc, Term)
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
