module Main where

import qualified Data.Map as Map

import Data.Maybe
import Data.Foldable
import Control.Monad.State

import Bwd
import Parse
import Term
import Thin
import Display
import Syntax
import Command

data SystemState = SystemState
  { syntaxTable :: Map.Map SyntaxCat SyntaxDesc
  }
  deriving Show


initState :: SystemState
initState = SystemState
  { syntaxTable = Map.fromList [("syntax", syntaxDesc)
                               ,("command", commandDesc)
                               ]
  }

command :: Command -> State SystemState Response
command c = do
  st <- gets syntaxTable
  if not (validate st B0 (rec "command") c)
    then return (atom "MisformedCommandError" 0)
    else fromJust $ ($ c) $ asTagged $ \case
      ("SYNTAX",_) -> asPair $ asList $ \ ss -> asNil $ Just $ do
        traverse updateSyntaxTable ss
        return (atom "AyeAyeCaptain" 0)
      _ -> \ _ -> Just $ return (atom "UnknownCommandError" 0)
  where
    updateSyntaxTable :: CdB (Tm Meta) -> State SystemState ()
    updateSyntaxTable = fromJust . (asPair $ asAtom $ \ (name, _) syn -> Just (modify (\ state -> state {syntaxTable = Map.insert name syn (syntaxTable state)})))

terms :: String -> [Term]
terms s = case parser (pspc *> ptm <* pnl) B0 s of
  [(t,s)] -> (fmap shitMeta $^ t):(terms s)
  _ -> (error $ "Unparsed input: " ++ s) `seq` []


testing = map fst $ Map.toList $ syntaxTable $ execState (command (fmap shitMeta $^ parse ptm lamSyntax)) initState where
  lamSyntax
    = "['SYNTAX '[['chk | ['Tag '[ ['Lam | '[['Bind 'syn ['Rec 'chk]]] ]\
                                  \['Emb | '[ ['Rec 'syn] ] ] ]]]\
                 \['syn | ['Tag '[ ['Rad | '[ ['Rec 'chk] ['Rec 'typ] ] ]\
                                  \['App | '[ ['Rec 'syn] ['Rec 'chk] ] ] ]]]\
                 \['typ | ['Tag '[ ['Base | '[]] ['Arrow | '[ ['Rec 'typ] ['Rec 'typ] ] ] ]]]\
      \]]"


main :: IO ()
main = do
  s <- getContents
  let ts = evalState (traverse command (terms s)) initState
  for_ ts $ \ t ->
    putStrLn (display' initNaming t)

{-
test = display' initNaming (fst (head (parser (pspc *> ptm) B0 (display' initNaming syntaxDesc)))) == display' initNaming syntaxDesc
-}
