module Concrete.Base where

import Bwd
import Format
import Scope

newtype Variable = Variable { getVariable :: String }
  deriving (Show, Eq)
type Atom = String

data Raw
  = Var Variable
  | At Atom
  | Cons Raw Raw
  | Lam (Scope Raw)
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
  | LamP (Scope RawP)
  | ThP (Bwd Variable, ThDirective) RawP
  | UnderscoreP
  deriving (Show)

data ThDirective = ThKeep | ThDrop
  deriving (Show)

data Actor
 = Actor :|: Actor
 | Spawn Variable Variable Actor
 | Send Variable Raw Actor
 | Recv Variable (Variable, Actor)
 | FreshMeta Raw (Variable, Actor)
 | Under (Scope Actor)
 | Match Raw [(RawP, Actor)]
 -- This is going to bite us when it comes to dependent types
 | Constrain Raw Raw
 | Push Variable (Variable, Raw) Actor
 | Lookup Raw (Variable, Actor) Actor
 | Win
 | Fail  [Format Directive Debug Raw]
 | Print [Format Directive Debug Raw] Actor
 | Break [Format Directive Debug Raw] Actor
 deriving (Show)
