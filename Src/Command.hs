module Command where

import Thin
import Term
import Syntax
import Parse
import Term.Parse

type Command = Term
type Response = Term

modeDesc :: SyntaxDesc
modeDesc = fmap shitMeta $^ parse ptm
  "['Enum '[ 'Input 'Subject 'Output ]]"

commandDesc :: SyntaxDesc
commandDesc = fmap shitMeta $^ parse ptm
  "['Tag '[\
           \ ['SYNTAX| '[['Fix \\list.['Tag '[['Nil| '[]] ['Cons| '[['Cons ['Atom] ['Rec 'syntax]] list]]]]]]]\
           \ ['PRINT | '[['Term]] ]\
           \ ['JUDGEMENT | '[ ['Atom] ['Fix \\list.['Tag '[['Nil| '[]] ['Cons| '[['Cons ['Atom] ['Rec 'mode]] list]]]]]] ]\
           \] ]"

termDesc :: SyntaxDesc
termDesc = fmap shitMeta $^ parse ptm "['Term]"
