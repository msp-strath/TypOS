module Concrete.Base where

import Bwd
import Format
import Scope
import Location

newtype Variable = Variable { getVariable :: String }
  deriving (Show, Eq)
type Atom = String

data Binder x
  = Used x
  | Unused
  deriving (Show, Functor, Foldable, Traversable)

mkBinder :: Variable -> Binder Variable
mkBinder (Variable "_") = Unused
mkBinder v = Used v

data Raw
  = Var Range Variable
  | At Range Atom
  | Cons Range Raw Raw
  | Lam Range (Scope (Binder Variable) Raw)
  | Sbst Range (Bwd SbstC) Raw
  deriving (Show)

instance HasRange Raw where
  setRange r = \case
    Var _ v -> Var r v
    At _ a -> At r a
    Cons _ p q -> Cons r p q
    Lam _ sc -> Lam r sc
    Sbst _ sg t -> Sbst r sg t

  getRange = \case
    Var r v -> r
    At r a -> r
    Cons r p q -> r
    Lam r sc -> r
    Sbst r sg t -> r

data SbstC
  = Keep Variable
  | Drop Variable
  | Assign Variable Raw
  deriving (Show)

data RawP
  = VarP Range Variable
  | AtP Range Atom
  | ConsP Range RawP RawP
  | LamP Range (Scope (Binder Variable) RawP)
  | ThP Range (Bwd Variable, ThDirective) RawP
  | UnderscoreP Range
  deriving (Show)

instance HasRange RawP where
  setRange r = \case
    VarP _ v -> VarP r v
    AtP _ a -> AtP r a
    ConsP _ p q -> ConsP r p q
    LamP _ sc -> LamP r sc
    ThP _ sg t -> ThP r sg t
    UnderscoreP _ -> UnderscoreP r

  getRange = \case
    VarP r v -> r
    AtP r a -> r
    ConsP r p q -> r
    LamP r sc -> r
    ThP r sg t -> r
    UnderscoreP r -> r

data ThDirective = ThKeep | ThDrop
  deriving (Show)

data Mode = Input | {- Subject | -} Output
  deriving (Show, Eq)

type Protocol t = [(Mode, t)]

data JudgementStack t = JudgementStack
  { keyDesc :: t
  , valueDesc :: t
  } deriving (Show, Functor, Foldable, Traversable)

data CConnect = CConnect Variable Variable
  deriving (Show)

data ExtractMode
  = AlwaysExtract
  | TopLevelExtract
  | InterestingExtract
  deriving (Show, Eq)

data Actor jd ch bd av syn var tm pat cnnct stk
 = Actor jd ch bd av syn var tm pat cnnct stk :|: Actor jd ch bd av syn var tm pat cnnct stk
 | Spawn ExtractMode jd ch (Actor jd ch bd av syn var tm pat cnnct stk)
 | Send ch tm (Actor jd ch bd av syn var tm pat cnnct stk)
 | Recv ch (bd, Actor jd ch bd av syn var tm pat cnnct stk)
 | Connect cnnct
 | Note (Actor jd ch bd av syn var tm pat cnnct stk)
 | FreshMeta syn (av, Actor jd ch bd av syn var tm pat cnnct stk)
 | Under (Scope String (Actor jd ch bd av syn var tm pat cnnct stk))
 | Match tm [(pat, Actor jd ch bd av syn var tm pat cnnct stk)]
 -- This is going to bite us when it comes to dependent types
 | Constrain tm tm
 | Push jd (var, stk, tm) (Actor jd ch bd av syn var tm pat cnnct stk)
 | Lookup tm (bd, Actor jd ch bd av syn var tm pat cnnct stk) (Actor jd ch bd av syn var tm pat cnnct stk)
 | Win
 | Fail  [Format Directive Debug tm]
 | Print [Format Directive Debug tm] (Actor jd ch bd av syn var tm pat cnnct stk)
 | Break [Format Directive Debug tm] (Actor jd ch bd av syn var tm pat cnnct stk)
 deriving (Show)

isWin :: Actor jd ch bd av syn var tm pat cnnct stk -> Bool
isWin Win = True
isWin _ = False

type CProtocol = Protocol Raw
type CJudgementStack = JudgementStack Raw
type CActor = Actor Variable Variable (Binder Variable) Variable Raw Variable Raw RawP CConnect ()
