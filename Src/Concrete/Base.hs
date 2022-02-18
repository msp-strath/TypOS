module Concrete.Base where

import Bwd
import Format
import Scope

type Variable = String
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
  deriving (Show)

data ThDirective = ThKeep | ThDrop
  deriving (Show)

data Actor
 = Actor :|: Actor
 | Spawn Variable Variable Actor
 | Send Variable Raw Actor
 | Recv Variable Variable Actor
 | FreshMeta Variable Actor
 | Under (Scope Actor)
 | Match (Maybe String) Raw [(RawP, Actor)]
 -- This is going to bite us when it comes to dependent types
 | Constrain Raw Raw
 | Extend (Variable, String, Variable, Actor) Actor
 | Fail String
 | Win
 | Print [Format Directive Debug Raw] Actor
 | Break String Actor
 deriving (Show)