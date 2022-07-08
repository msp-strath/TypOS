{-# LANGUAGE UndecidableInstances #-}
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

instance HasSetRange Variable where
  setRange r (Variable _ v) = Variable r v
instance HasGetRange Variable where
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

instance HasSetRange Raw where
  setRange r = \case
    Var _ v -> Var r v
    At _ a -> At r a
    Cons _ p q -> Cons r p q
    Lam _ sc -> Lam r sc
    Sbst _ sg t -> Sbst r sg t

instance Eq Raw where
  Var _ v == Var _ w = v == w
  At _ a == At _ b = a == b
  Cons _ p q == Cons _ s t = p == s && q == t
  Lam _ sc == Lam _ bd = sc == bd
  Sbst _ cs t == Sbst _ ds u = cs == ds && t == u
  _ == _ = False

instance HasGetRange Raw where
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

instance Eq SbstC where
  Keep _ v == Keep _ w = v == w
  Drop _ v == Drop _ w = v == w
  Assign _ v t == Assign _ w u = v == w && t == u
  _ == _ = False

instance HasSetRange SbstC where
  setRange r = \case
    Keep _ v -> Keep r v
    Drop _ v -> Drop r v
    Assign _ v t -> Assign r v t

instance HasGetRange SbstC where
  getRange = \case
    Keep r v -> r
    Drop r v -> r
    Assign r v t -> r

data RawP
  = AsP Range Variable RawP
  | VarP Range Variable
  | AtP Range Atom
  | ConsP Range RawP RawP
  | LamP Range (Scope (Binder Variable) RawP)
  | ThP Range (Bwd Variable, ThDirective) RawP
  | UnderscoreP Range
  deriving (Show)

instance HasSetRange RawP where
  setRange r = \case
    AsP _ v p -> AsP r v p
    VarP _ v -> VarP r v
    AtP _ a -> AtP r a
    ConsP _ p q -> ConsP r p q
    LamP _ sc -> LamP r sc
    ThP _ sg t -> ThP r sg t
    UnderscoreP _ -> UnderscoreP r

instance HasGetRange RawP where
  getRange = \case
    AsP r _ _ -> r
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

data ContextStack t = ContextStack
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

data Keyword
  = KwSyntax | KwExec | KwTrace
  | KwLet | KwCase | KwLookup | KwCompare
  | KwBREAK | KwPRINT | KwPRINTF
  deriving (Enum, Bounded)

instance Show Keyword where
  show KwSyntax = "syntax"
  show KwExec = "exec"
  show KwTrace = "trace"
  show KwLet = "let"
  show KwCase = "case"
  show KwLookup = "lookup"
  show KwCompare = "compare"
  show KwBREAK = "BREAK"
  show KwPRINT = "PRINT"
  show KwPRINTF = "PRINTF"

data Phase = Concrete | Abstract

type family JUDGEMENTFORM (ph :: Phase) :: *
type family CHANNEL (ph :: Phase) :: *
type family BINDER (ph :: Phase) :: *
type family ACTORVAR (ph :: Phase) :: *
type family SYNTAXDESC (ph :: Phase) :: *
type family TERMVAR (ph :: Phase) :: *
type family TERM (ph :: Phase) :: *
type family PATTERN (ph :: Phase) :: *
type family CONNECT (ph :: Phase) :: *
type family STACK (ph :: Phase) :: *
type family STACKDESC (ph :: Phase) :: *

type instance JUDGEMENTFORM Concrete = Variable
type instance CHANNEL Concrete = Variable
type instance BINDER Concrete = RawP
type instance ACTORVAR Concrete = Variable
type instance SYNTAXDESC Concrete = Raw
type instance TERMVAR Concrete = Variable
type instance TERM Concrete = Raw
type instance PATTERN Concrete = RawP
type instance CONNECT Concrete = CConnect
type instance STACK Concrete = Variable
type instance STACKDESC Concrete = ()

type FORMAT (ph :: Phase) = [Format Directive Debug (TERM ph)]

data SCRUTINEE (ph :: Phase)
 = Term Range (TERM ph)
 | Pair Range (SCRUTINEE ph) (SCRUTINEE ph)
 | Lookup Range (STACK ph) (TERM ph)
 | Compare Range (TERM ph) (TERM ph)

isProper :: SCRUTINEE ph -> Bool
isProper Term{} = False
isProper (Pair _ s t) = isProper s || isProper t
isProper Lookup{} = True
isProper Compare{} = True

instance HasSetRange (SCRUTINEE ph) where
  setRange r = \case
    Term _ t -> Term r t
    Pair _ p q -> Pair r p q
    Lookup _ stk t -> Lookup r stk t
    Compare _ s t -> Compare r s t

instance HasGetRange (SCRUTINEE ph) where
  getRange = \case
    Term r t -> r
    Pair r p q -> r
    Lookup r stk t -> r
    Compare r s t -> r

data ACTOR (ph :: Phase)
 = Branch Range (ACTOR ph) (ACTOR ph)
 | Spawn Range ExtractMode (JUDGEMENTFORM ph) (CHANNEL ph) (ACTOR ph)
 | Send Range (CHANNEL ph) (TERM ph) (ACTOR ph)
 | Recv Range (CHANNEL ph) (BINDER ph, ACTOR ph)
 | Connect Range (CONNECT ph)
 | Note Range (ACTOR ph)
 | FreshMeta Range (SYNTAXDESC ph) (ACTORVAR ph, ACTOR ph)
 | Let Range (ACTORVAR ph) (SYNTAXDESC ph) (TERM ph) (ACTOR ph)
 | Under Range (Scope Variable (ACTOR ph))
 | Match Range (SCRUTINEE ph) [(PATTERN ph, ACTOR ph)]
 -- This is going to bite us when it comes to dependent types
 | Constrain Range (TERM ph) (TERM ph)
 | Push Range (STACK ph) (TERMVAR ph, STACKDESC ph, TERM ph) (ACTOR ph)
 | Win Range
 | Fail  Range (FORMAT ph)
 | Print Range (FORMAT ph) (ACTOR ph)
 | Break Range (FORMAT ph) (ACTOR ph)

deriving instance
  ( Show (TERM ph)
  , Show (STACK ph)) =>
  Show (SCRUTINEE ph)

deriving instance
  ( Show (JUDGEMENTFORM ph)
  , Show (CHANNEL ph)
  , Show (BINDER ph)
  , Show (ACTORVAR ph)
  , Show (SYNTAXDESC ph)
  , Show (TERMVAR ph)
  , Show (TERM ph)
  , Show (PATTERN ph)
  , Show (CONNECT ph)
  , Show (STACK ph)
  , Show (STACKDESC ph)) =>
  Show (ACTOR ph)

instance HasSetRange (ACTOR ph) where
  setRange r = \case
    Branch _ a b -> Branch r a b
    Spawn _ em jd ch ac -> Spawn r em jd ch ac
    Send _ ch tm ac -> Send r ch tm ac
    Recv _ ch x0 -> Recv r ch x0
    Connect _ cnnct -> Connect r cnnct
    Note _ ac -> Note r ac
    FreshMeta _ syn x0 -> FreshMeta r syn x0
    Let _ x d t a -> Let r x d t a
    Under _ sc -> Under r sc
    Match _ tm x0 -> Match r tm x0
    Constrain _ tm tm' -> Constrain r tm tm'
    Push _ jd x0 ac -> Push r jd x0 ac
    Win _ -> Win r
    Fail _ fors -> Fail r fors
    Print _ fors ac -> Print r fors ac
    Break _ fors ac -> Break r fors ac

instance HasGetRange (ACTOR ph) where
  getRange = \case
    Branch r a b -> r
    Spawn r em jd ch ac -> r
    Send r ch tm ac -> r
    Recv r ch x0 -> r
    Connect r cnnct -> r
    Note r ac -> r
    FreshMeta r syn x0 -> r
    Let r _ _ _ _ -> r
    Under r sc -> r
    Match r tm x0 -> r
    Constrain r tm tm' -> r
    Push r jd x0 ac -> r
    Win r -> r
    Fail r fors -> r
    Print r fors ac -> r
    Break r fors ac -> r

isWin :: ACTOR ph -> Bool
isWin (Win _) = True
isWin _ = False

type CProtocol = Protocol Raw
type CContextStack = ContextStack Raw
type CActor = ACTOR Concrete
type CScrutinee = SCRUTINEE Concrete
