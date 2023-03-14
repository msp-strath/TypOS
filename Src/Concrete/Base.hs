{-# LANGUAGE UndecidableInstances #-}
module Concrete.Base where

import Data.Function (on)

import Bwd
import Format
import Scope
import Location
import Data.Bifunctor (Bifunctor (..))

data Variable = Variable
  { variableLoc :: Range
  , getVariable :: String
  }
instance Show Variable where show = show . getVariable
instance Eq Variable where (==) = (==) `on` getVariable
instance Ord Variable where compare = compare `on` getVariable

instance HasSetRange Variable where
  setRange r (Variable _ v) = Variable r v
instance HasGetRange Variable where
  getRange = variableLoc

type Atom = String

type Root = ( Bwd (String, Int) -- name prefix
            , Int)              -- counter

-- Identifier for guard which denotes if a term is safe to use
type Guard = Root

data Binder x
  = Used x
  | Unused
  deriving (Show, Functor, Foldable, Traversable)

mkBinder :: Variable -> Binder Variable
mkBinder (Variable r "_") = Unused
mkBinder v = Used v

{-
getBinder :: Binder Variable -> Variable
getBinder (Used v) = v
getBinder Unused = Variable unknown "_"
-}

data Raw
  = Var Range Variable
  | At Range Atom
  | Cons Range Raw Raw
  | Lam Range (Scope (Binder Variable) Raw)
  | Sbst Range (Bwd Assign) Raw
  | Op Range Raw Raw
  | Guarded Guard Raw
  | Thicken Range (Bwd Variable, ThDirective) Raw
  deriving (Show)

instance HasSetRange Raw where
  setRange r = \case
    Var _ v -> Var r v
    At _ a -> At r a
    Cons _ p q -> Cons r p q
    Lam _ sc -> Lam r sc
    Sbst _ sg t -> Sbst r sg t
    Op _ s t -> Op r s t
    t@Guarded{} -> t
    Thicken _ th t -> Thicken r th t

instance Eq Raw where
  Var _ v == Var _ w = v == w
  At _ a == At _ b = a == b
  Cons _ p q == Cons _ s t = p == s && q == t
  Lam _ sc == Lam _ bd = sc == bd
  Sbst _ cs t == Sbst _ ds u = cs == ds && t == u
  Op _ s t == Op _ a b = s == a && t == b
  Guarded g t == Guarded h u = (g, t) == (h, u)
  Thicken _ th t == Thicken _ ph u = (th, t) == (ph, u)
  _ == _ = False

instance HasGetRange Raw where
  getRange = \case
    Var r _ -> r
    At r _ -> r
    Cons r _ _ -> r
    Lam r _ -> r
    Sbst r _ _ -> r
    Op r _ _ -> r
    Guarded _ t -> getRange t
    Thicken r _ _ -> r

data Assign = Assign
  { assignRange :: Range
  , assignVariable :: Variable
  , assignTerm :: Raw
  } deriving (Show)

instance Eq Assign where
  Assign _ v t == Assign _ w u = v == w && t == u

instance HasSetRange Assign where
  setRange r (Assign _ v t) = Assign r v t

instance HasGetRange Assign where
  getRange = assignRange

data RawP
  = AsP Range Variable RawP
  | VarP Range Variable
  | AtP Range Atom
  | ConsP Range RawP RawP
  | LamP Range (Scope (Binder Variable) RawP)
  | ThP Range (Bwd Variable, ThDirective) RawP
  | UnderscoreP Range
  | Irrefutable Range RawP
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
    Irrefutable _ p -> Irrefutable r p

instance HasGetRange RawP where
  getRange = \case
    AsP r _ _ -> r
    VarP r v -> r
    AtP r a -> r
    ConsP r p q -> r
    LamP r sc -> r
    ThP r sg t -> r
    UnderscoreP r -> r
    Irrefutable r p -> r

data ThDirective = ThKeep | ThDrop
  deriving (Show, Eq)

data Mode a = Input | Subject a | Output
  deriving (Show, Eq, Functor, Foldable, Traversable)

isSubjectMode :: Mode a -> Bool
isSubjectMode (Subject _) = True
isSubjectMode _           = False

type family SYNTAXDESC (ph :: Phase) :: *
type instance SYNTAXDESC Concrete = Raw
type CSyntaxDesc = SYNTAXDESC Concrete
type ASyntaxDesc = SYNTAXDESC Abstract

type family SEMANTICSDESC (ph :: Phase)
type instance SEMANTICSDESC Concrete = Raw

type CSemanticsDesc = SEMANTICSDESC Concrete
type ASemanticsDesc = SEMANTICSDESC Abstract

type PROTOCOLENTRY (ph :: Phase) = (Mode (SYNTAXDESC ph), SEMANTICSDESC ph)
type CProtocolEntry = PROTOCOLENTRY Concrete
type AProtocolEntry = PROTOCOLENTRY Abstract

newtype PROTOCOL (ph :: Phase) = Protocol {getProtocol :: [PROTOCOLENTRY ph]}

deriving instance
  ( Show (SYNTAXDESC ph)
  , Show (SEMANTICSDESC ph)) => Show (PROTOCOL ph)

data ContextStack k v = ContextStack
  { keyDesc :: k {- syntax desc -}
  , valueDesc :: v {- closed semantics desc -}
  } deriving (Show)

instance Bifunctor ContextStack where
  bimap f g (ContextStack k v) = ContextStack (f k) (g v)

data CConnect = CConnect Variable Variable
  deriving (Show)

data ExtractMode
  = AlwaysExtract
  | TopLevelExtract
  | InterestingExtract
  deriving (Show, Eq)

data Keyword
  = KwSyntax | KwRule | KwJudgementForm | KwExec | KwTrace
  | KwLet | KwCase | KwLookup | KwCompare
  | KwBREAK | KwPRINT | KwPRINTF
  deriving (Enum, Bounded)

instance Show Keyword where
  show KwSyntax = "syntax"
  show KwRule = "rule"
  show KwJudgementForm = "judgementform"
  show KwExec = "exec"
  show KwTrace = "trace"
  show KwLet = "let"
  show KwCase = "case"
  show KwLookup = "lookup"
  show KwCompare = "compare"
  show KwBREAK = "BREAK"
  show KwPRINT = "PRINT"
  show KwPRINTF = "PRINTF"

data Phase = Concrete | Elaboration | Abstract

type family JUDGEMENTNAME (ph :: Phase) :: *
type family CHANNEL (ph :: Phase) :: *
type family BINDER (ph :: Phase) :: *
type family ACTORVAR (ph :: Phase) :: *
type family TERMVAR (ph :: Phase) :: *
type family TERM (ph :: Phase) :: *
type family PATTERN (ph :: Phase) :: *
type family CONNECT (ph :: Phase) :: *
type family STACK (ph :: Phase) :: *
type family STACKDESC (ph :: Phase) :: *
type family SCRUTINEEVAR (ph :: Phase) :: *
type family SCRUTINEETERM (ph :: Phase) :: *
type family LOOKEDUP (ph :: Phase) :: *
type family GUARD (ph :: Phase) :: *

type instance JUDGEMENTNAME Concrete = Variable
type instance CHANNEL Concrete = Variable
type instance BINDER Concrete = RawP
type instance ACTORVAR Concrete = Variable
type instance TERMVAR Concrete = Variable
type instance TERM Concrete = Raw
type instance PATTERN Concrete = RawP
type instance CONNECT Concrete = CConnect
type instance STACK Concrete = Variable
type instance STACKDESC Concrete = ()
type instance SCRUTINEEVAR Concrete = Variable
type instance SCRUTINEETERM Concrete = Raw
type instance LOOKEDUP Concrete = Variable
type instance GUARD Concrete = ()

type FORMAT (ph :: Phase) = [Format Directive Debug (TERM ph)]

data SCRUTINEE (ph :: Phase)
  = SubjectVar Range (SCRUTINEEVAR ph)
  | Term Range (SCRUTINEETERM ph)
  | Pair Range (SCRUTINEE ph) (SCRUTINEE ph)
  | Lookup Range (STACK ph) (LOOKEDUP ph)
  | Compare Range (TERM ph) (TERM ph)

instance HasSetRange (SCRUTINEETERM ph) => HasSetRange (SCRUTINEE ph) where
  setRange r = \case
    SubjectVar _ v -> SubjectVar r v
    Term _ t -> Term r (setRange r t)
    Pair _ p q -> Pair r p q
    Lookup _ stk t -> Lookup r stk t
    Compare _ s t -> Compare r s t

instance HasGetRange (SCRUTINEE ph) where
  getRange = \case
    SubjectVar r t -> r
    Term r t -> r
    Pair r p q -> r
    Lookup r stk t -> r
    Compare r s t -> r

data ACTOR (ph :: Phase)
 = Branch Range (ACTOR ph) (ACTOR ph)
 | Spawn Range ExtractMode (JUDGEMENTNAME ph) (CHANNEL ph) (ACTOR ph)
 | Send Range (CHANNEL ph) (GUARD ph) (TERM ph) (ACTOR ph)
 | Recv Range (CHANNEL ph) (BINDER ph, ACTOR ph)
 | Connect Range (CONNECT ph)
 | Note Range (ACTOR ph)
 | FreshMeta Range (SEMANTICSDESC ph) (ACTORVAR ph, ACTOR ph)
 | Let Range (ACTORVAR ph) (SEMANTICSDESC ph) (TERM ph) (ACTOR ph)
 | Under Range (Maybe (SEMANTICSDESC ph)) (Scope Variable (ACTOR ph))
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
  , Show (SCRUTINEEVAR ph)
  , Show (SCRUTINEETERM ph)
  , Show (STACK ph)
  , Show (LOOKEDUP ph)) =>
  Show (SCRUTINEE ph)

deriving instance
  ( Show (JUDGEMENTNAME ph)
  , Show (CHANNEL ph)
  , Show (BINDER ph)
  , Show (ACTORVAR ph)
  , Show (SCRUTINEEVAR ph)
  , Show (SCRUTINEETERM ph)
  , Show (SEMANTICSDESC ph)
  , Show (TERMVAR ph)
  , Show (TERM ph)
  , Show (PATTERN ph)
  , Show (CONNECT ph)
  , Show (STACK ph)
  , Show (STACKDESC ph)
  , Show (LOOKEDUP ph)
  , Show (GUARD ph)) =>
  Show (ACTOR ph)

instance HasSetRange (ACTOR ph) where
  setRange r = \case
    Branch _ a b -> Branch r a b
    Spawn _ em jd ch ac -> Spawn r em jd ch ac
    Send _ ch gd tm ac -> Send r ch gd tm ac
    Recv _ ch x0 -> Recv r ch x0
    Connect _ cnnct -> Connect r cnnct
    Note _ ac -> Note r ac
    FreshMeta _ syn x0 -> FreshMeta r syn x0
    Let _ x d t a -> Let r x d t a
    Under _ mty sc -> Under r mty sc
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
    Send r ch gd tm ac -> r
    Recv r ch x0 -> r
    Connect r cnnct -> r
    Note r ac -> r
    FreshMeta r syn x0 -> r
    Let r _ _ _ _ -> r
    Under r mty sc -> r
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

type CProtocol = PROTOCOL Concrete
type CContextStack = ContextStack Raw Raw
type CActor = ACTOR Concrete
type CScrutinee = SCRUTINEE Concrete
