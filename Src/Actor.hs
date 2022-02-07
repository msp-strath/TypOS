module Actor where

import qualified Data.Map as Map

import Hide
import Scope
import Bwd
import Term
import Pattern
import Thin
import ANSI

type ActorVar = String

data ActorMeta = ActorMeta ActorVar
  deriving (Eq, Ord)

instance Show ActorMeta where
  show (ActorMeta str) = str

data PatVar = VarP Int
  deriving (Show, Eq)

instance Thable PatVar where
  VarP i *^ th = VarP (i *^ th)

data Channel = Channel String deriving (Eq)
instance Show Channel  where show (Channel str)  = str

type MatchLabel = String
type JudgementForm = String
type Gripe = String

data Env = Env
  { scopeEnv  :: Int
  , actorVars :: Map.Map ActorMeta ([String], Term)
  } deriving (Show, Eq)

initEnv :: Int -> Env
initEnv gamma = Env gamma Map.empty

newActorVar :: ActorMeta -> ([String], Term) -> Env -> Env
newActorVar x defn env@(Env _ avs) = env { actorVars = Map.insert x defn avs }

instance Thable Env where
  Env sc avs *^ th = Env (bigEnd th) (fmap thinDefn avs) where

    thinDefn :: ([String], Term) -> ([String], Term)
    thinDefn (xs, (t, ph)) = (xs, (t, ph <^> (th <> ones (length xs))))

weakenEnv :: Int -> Env -> Env
weakenEnv i rho = rho *^ (ones (scopeEnv rho) <> none i)

type PatActor = PatF PatVar

infixr 3 :|:
-- We expect all the terms to be closed
data Actor
 = Actor :|: Actor
 | Closure Env Actor
 | Spawn JudgementForm Channel Actor
 | Send Channel (CdB (Tm ActorMeta)) Actor
 | Recv Channel ActorMeta Actor
 | FreshMeta ActorMeta Actor
 | Under (Scope Actor)
 | Match MatchLabel (CdB (Tm ActorMeta)) [(PatActor, Actor)]
 -- This is going to bite us when it comes to dependent types
 | Constrain (CdB (Tm ActorMeta)) (CdB (Tm ActorMeta))
 | Extend (JudgementForm, MatchLabel, PatVar, Actor) Actor
 | Fail Gripe
 | Win
 | Break String Actor
 deriving (Show, Eq)

instance Thable Actor where
  a *^ th = case a of
    a :|: b -> a *^ th :|: b *^ th
    Closure rho a -> Closure (rho *^ th) (a *^ th)
    Spawn jd ch a -> Spawn jd ch (a *^ th)
    Send ch t a -> Send ch (t *^ th) (a *^ th)
    Recv ch av a -> Recv ch av (a *^ th)
    FreshMeta av a -> FreshMeta av (a *^ th)
    Under sc -> Under (sc *^ th)
    Match ml t pas -> Match ml (t *^ th) (map (fmap (*^ th)) pas)
    Constrain s t -> Constrain (s *^ th) (t *^ th)
    Extend (jd, ml, pv, a) b -> Extend (jd, ml, pv *^ th, a *^ th) (b *^ th)
    Fail gr -> Fail gr
    Win -> Win
    Break str a -> Break str (a *^ th)

mangleActors :: Env                {- Env ga -}
                                   {- ga ~ ga0 <<< de -}
             -> CdB (Tm ActorMeta) {- Src de -}
             -> Maybe Term         {- Trg ga -}
mangleActors env@(Env ga _) initm = go initm

 where
  ga0 :: Int
  ga0 = ga - scope initm

  go :: CdB (Tm ActorMeta) {- Src (de <<< de') -}
     -> Maybe Term         {- Trg (ga <<< de') -}
  go tm = let gade' = ga0 + scope tm in case expand tm of
    VX i _ -> pure $ var i gade'
    AX s _ -> pure $ atom s gade'
    a :%: b -> (%) <$> go a <*> go b
    x :.: t -> (x \\) <$> go t
    m :$: sbst -> do
      (xs, t) <- noisyLookupVar m
      let xi = B0 <>< xs
      sg <- goSbst xi sbst
      pure (t //^ sg)

  goSbst :: Bwd String           {- xi -}
         -> CdB (Sbst ActorMeta) {-        xi =>Src de <<< de' -}
         -> Maybe Subst          {- ga <<< xi =>Trg ga <<< de' -}
  goSbst B0 (S0 :^^ 0, th)
    = pure (S0 :^^ ga, ones ga <> none (bigEnd th - scope initm))
                                 -- ^ |de <<< de'| - |de| = |de'|
  goSbst nz (ST rp :^^ 0, th) =
    splirp (rp, th) $ \ s (x := tm, ph) -> do
      nz <- nz `covers` x
      s <- goSbst nz s
      tm <- go (tm, ph)
      pure $ sbstT s ((x :=) $^ tm)
  goSbst nz (sbst :^^ w, th) = do
    let (thw, ps) = chopTh w th
    sg <- goSbst (dropz nz w) (sbst :^^ 0, thw)
    pure $ sbstW sg ps

  -- Return the term associated to an actor var, together with the
  -- local scope extension it was bound in. We expect that the
  -- substitution acting upon the term will cover all of these local
  -- variables.
  lookupVar :: Env -> ActorMeta -> Maybe ([String], Term)
  lookupVar (Env sc avs) av = Map.lookup av avs

  -- `covers nz x` ensures that `x` is at the most local end of `nz`.
  covers :: Bwd String -> Hide String -> Maybe (Bwd String)
  covers (nz :< n) (Hide x)
    | n == x = pure nz
    | otherwise = let msg = "Subst mismatch: expected " ++ n ++ " got " ++ x in
                  alarm msg (pure nz)
  covers nz _ = pure nz

  noisyLookupVar :: ActorMeta -> Maybe ([String], Term)
  noisyLookupVar av = case lookupVar env av of
    Just xst -> Just xst
    Nothing -> alarm ("couldn't find " ++ show av ++ " in " ++ show env) Nothing
