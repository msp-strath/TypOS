{-# LANGUAGE FlexibleInstances #-}

module Main where

import qualified Data.Map as Map

import Data.Maybe
import Data.Foldable
import Control.Monad.State

import Actor
import Bwd
import Parse
import Term
import Thin
import Display
import Syntax
import Command

data Mode = Input | Subject | Output deriving (Eq, Show)

data SystemState = SystemState
  { syntaxTable :: Map.Map SyntaxCat SyntaxDesc
  , judgementTable :: Map.Map JudgementForm [(SyntaxCat,Mode)]
  }
  deriving Show


initState :: SystemState
initState = SystemState
  { syntaxTable = Map.fromList [("syntax", syntaxDesc)
                               ,("command", commandDesc)
                               ,("mode", modeDesc)
                               ,("term", termDesc)
                               ]
  , judgementTable = Map.singleton "guess" [("term",Output)]
  }

instance OrBust x => OrBust (State s x) where
  bust = pure bust

instance OrBust Response where
  bust = atom "BustError" 0

instance OrBust () where
  bust = ()

asMode :: OrBust x => (Mode -> x) -> CdB (Tm m) -> x
asMode f = asAtom $ \case
  ("Input",_) -> f Input
  ("Subject",_) -> f Subject
  ("Output",_) -> f Output
  _ -> bust

command :: Command -> State SystemState Response
command c = do
  st <- gets syntaxTable
  if not (validate st B0 (rec "command") c)
    then return (atom "MisformedCommandError" 0)
    else ($ c) $ asTagged $ \case
      ("SYNTAX",_) -> asPair $ asList $ \ ss -> asNil $ do
        traverse updateSyntaxTable ss
        return (atom "SyntaxAdded" 0)
      ("PRINT",_) -> asPair $ \ t -> asNil $ return t
      ("JUDGEMENT",_) -> asPair $ asAtom $ \ (j,_) -> asPair $ asList $ \ ss -> asNil $
        case traverse (validateJudgementPos st) ss of
          Nothing ->  pure $ atom "SyntaxCatNotFoundError" 0
          Just xs -> do modify $ \st -> st { judgementTable = Map.insert j xs (judgementTable st) }
                        return (atom "JudgementAdded" 0)

      _ -> \ _ -> return (atom "UnknownCommandError" 0)
  where
    updateSyntaxTable :: CdB (Tm Meta) -> State SystemState ()
    updateSyntaxTable = asPair $ asAtom $ \ (name, _) syn -> modify (\ state -> state {syntaxTable = Map.insert name syn (syntaxTable state)})

    validateJudgementPos :: SyntaxTable -> CdB (Tm Meta) -> Maybe (SyntaxCat,Mode)
    validateJudgementPos tbl = asPair $ asAtom $ \(cat,_) -> asMode $ \ m -> (cat,m) <$ Map.lookup cat tbl

terms :: String -> [Term]
terms s = case parser (pspc *> ptm <* pnl) B0 s of
  [(t,s)] -> (fmap shitMeta $^ t):terms s
  _ -> error ("Unparsed input: " ++ s) `seq` []


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
  putStrLn "Start typing now"
  s <- getContents
  let ts = evalState (traverse command (terms s)) initState
  for_ ts $ \ t ->
    putStrLn (display' initNaming t)

{-
test = display' initNaming (fst (head (parser (pspc *> ptm) B0 (display' initNaming syntaxDesc)))) == display' initNaming syntaxDesc
-}
