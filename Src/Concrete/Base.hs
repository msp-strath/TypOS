module Concrete.Base where

import Bwd
import Format
import Scope
import Location
import Data.Function (on)

data Variable = Variable
  { variableLoc :: Range
  , getVariable :: String
  }
instance Show Variable where show = show . getVariable
instance Eq Variable where (==) = (==) `on` getVariable

instance HasRange Variable where
  setRange r (Variable _ v) = Variable r v
  getRange = variableLoc

type Atom = String

data Binder x
  = Used x
  | Unused
  deriving (Show, Functor, Foldable, Traversable)

mkBinder :: Variable -> Binder Variable
mkBinder (Variable r "_") = Unused
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
  = Keep Range Variable
  | Drop Range Variable
  | Assign Range Variable Raw
  deriving (Show)

instance HasRange SbstC where
  setRange r = \case
    Keep _ v -> Keep r v
    Drop _ v -> Drop r v
    Assign _ v t -> Assign r v t

  getRange = \case
    Keep r v -> r
    Drop r v -> r
    Assign r v t -> r

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
 = Branch Range (Actor jd ch bd av syn var tm pat cnnct stk) (Actor jd ch bd av syn var tm pat cnnct stk)
 | Spawn Range ExtractMode jd ch (Actor jd ch bd av syn var tm pat cnnct stk)
 | Send Range ch tm (Actor jd ch bd av syn var tm pat cnnct stk)
 | Recv Range ch (bd, Actor jd ch bd av syn var tm pat cnnct stk)
 | Connect Range cnnct
 | Note Range (Actor jd ch bd av syn var tm pat cnnct stk)
 | FreshMeta Range syn (av, Actor jd ch bd av syn var tm pat cnnct stk)
 | Under Range (Scope Variable (Actor jd ch bd av syn var tm pat cnnct stk))
 | Match Range tm [(pat, Actor jd ch bd av syn var tm pat cnnct stk)]
 -- This is going to bite us when it comes to dependent types
 | Constrain Range tm tm
 | Push Range jd (var, stk, tm) (Actor jd ch bd av syn var tm pat cnnct stk)
 | Lookup Range tm (bd, Actor jd ch bd av syn var tm pat cnnct stk) (Actor jd ch bd av syn var tm pat cnnct stk)
 | Win Range
 | Fail  Range [Format Directive Debug tm]
 | Print Range [Format Directive Debug tm] (Actor jd ch bd av syn var tm pat cnnct stk)
 | Break Range [Format Directive Debug tm] (Actor jd ch bd av syn var tm pat cnnct stk)
 deriving (Show)

instance HasRange (Actor jd ch bd av syn var tm pat cnnct stk) where
  setRange r = \case
    Branch _ a b -> Branch r a b
    Spawn _ em jd ch ac -> Spawn r em jd ch ac
    Send _ ch tm ac -> Send r ch tm ac
    Recv _ ch x0 -> Recv r ch x0
    Connect _ cnnct -> Connect r cnnct
    Note _ ac -> Note r ac
    FreshMeta _ syn x0 -> FreshMeta r syn x0
    Under _ sc -> Under r sc
    Match _ tm x0 -> Match r tm x0
    Constrain _ tm tm' -> Constrain r tm tm'
    Push _ jd x0 ac -> Push r jd x0 ac
    Lookup _ tm x0 ac -> Lookup r tm x0 ac
    Win _ -> Win r
    Fail _ fors -> Fail r fors
    Print _ fors ac -> Print r fors ac
    Break _ fors ac -> Break r fors ac

  getRange = \case
    Branch r a b -> r
    Spawn r em jd ch ac -> r
    Send r ch tm ac -> r
    Recv r ch x0 -> r
    Connect r cnnct -> r
    Note r ac -> r
    FreshMeta r syn x0 -> r
    Under r sc -> r
    Match r tm x0 -> r
    Constrain r tm tm' -> r
    Push r jd x0 ac -> r
    Lookup r tm x0 ac -> r
    Win r -> r
    Fail r fors -> r
    Print r fors ac -> r
    Break r fors ac -> r

isWin :: Actor jd ch bd av syn var tm pat cnnct stk -> Bool
isWin (Win _) = True
isWin _ = False

type CProtocol = Protocol Raw
type CJudgementStack = JudgementStack Raw
type CActor = Actor Variable Variable (Binder Variable) Variable Raw Variable Raw RawP CConnect ()
