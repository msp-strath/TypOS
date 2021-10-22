module Command where

import Thin
import Term
import Syntax
import Parse

type Command = Term
type Response = Term

commandDesc :: SyntaxDesc
commandDesc = fmap shitMeta $^ parse ptm
  "['Tag '[\
           \ ['SYNTAX| '[['Fix \\list.['Tag '[['Nil| '[]] ['Cons| '[['Cons ['Atom] ['Rec 'syntax]] list]]]]]]]\
           \] ]"

