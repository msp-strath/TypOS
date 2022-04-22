module Concrete.Base where

import Bwd
import Format
import Scope

newtype Variable = Variable { getVariable :: String }
  deriving (Show, Eq)
type Atom = String

data Binder
  = Used String
  | Unused

data Raw
  = Var Variable
  | At Atom
  | Cons Raw Raw
  | Lam (Scope Binder Raw)
  | Sbst (Bwd SbstC) Raw
  deriving (Show)

data SbstC
  = Keep Variable
  | Drop Variable
  | Assign Variable Raw
  deriving (Show)

data RawP
  = VarP Variable
  | AtP Atom
  | ConsP RawP RawP
  | LamP (Scope Binder RawP)
  | ThP (Bwd Variable, ThDirective) RawP
  | UnderscoreP
  deriving (Show)

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

data Actor jd ch av syn var tm pat cnnct stk
 = Actor jd ch av syn var tm pat cnnct stk :|: Actor jd ch av syn var tm pat cnnct stk
 | Spawn ExtractMode jd ch (Actor jd ch av syn var tm pat cnnct stk)
 | Send ch tm (Actor jd ch av syn var tm pat cnnct stk)
 | Recv ch (av, Actor jd ch av syn var tm pat cnnct stk)
 | Connect cnnct
 | Note (Actor jd ch av syn var tm pat cnnct stk)
 | FreshMeta syn (av, Actor jd ch av syn var tm pat cnnct stk)
 | Under (Scope String (Actor jd ch av syn var tm pat cnnct stk))
 | Match tm [(pat, Actor jd ch av syn var tm pat cnnct stk)]
 -- This is going to bite us when it comes to dependent types
 | Constrain tm tm
 | Push jd (var, stk, tm) (Actor jd ch av syn var tm pat cnnct stk)
 | Lookup tm (av, Actor jd ch av syn var tm pat cnnct stk) (Actor jd ch av syn var tm pat cnnct stk)
 | Win
 | Fail  [Format Directive Debug tm]
 | Print [Format Directive Debug tm] (Actor jd ch av syn var tm pat cnnct stk)
 | Break [Format Directive Debug tm] (Actor jd ch av syn var tm pat cnnct stk)
 deriving (Show)

type CProtocol = Protocol Raw
type CJudgementStack = JudgementStack Raw
type CActor = Actor Variable Variable Variable Raw Variable Raw RawP CConnect ()
