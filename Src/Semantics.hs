{-# LANGUAGE GADTs #-}
module Semantics where

import Control.Monad
import Control.Applicative

import Data.Void
import Data.Map (Map)
import qualified Data.Map as Map

import Hide
import Bwd
import Concrete.Base (Phase(..), ASyntaxDesc, ASemanticsDesc, SEMANTICSDESC)
import Actor (ACTm, ActorMeta)
import Thin (CdB(..), DB(..), weak, scope, ($^), (*^), ones, none)
import Term hiding (contract, expand)
import qualified Term
import Syntax (SyntaxTable, SyntaxCat, WithSyntaxCat(..))
import Operator.Eval

embed :: ASyntaxDesc -> ASemanticsDesc
embed = (fmap absurd $^)

data VSemanticsDesc' a
  -- embedding syntax
  = VAtom Int
  | VAtomBar Int [String]
  | VNil Int
  | VCons ASemanticsDesc ASemanticsDesc
  | VNilOrCons ASemanticsDesc ASemanticsDesc
  | VBind SyntaxCat ASemanticsDesc
  | VEnumOrTag Int [String] [(String, [ASemanticsDesc])]
  | VWildcard Int
  | VSyntaxCat Int a
  -- stuck things
  | VNeutral ASemanticsDesc
  -- canonical semantics constructors
  | VUniverse Int
  | VPi ASemanticsDesc (String, ASemanticsDesc)
  deriving (Eq, Show)

type VSemanticsDesc = VSemanticsDesc' Void

extractScope :: VSemanticsDesc' a -> Int
extractScope = \case
  VAtom sc -> sc
  VAtomBar sc _ -> sc
  VNil sc -> sc
  VCons s t -> scope s
  VNilOrCons s t -> scope s
  VBind cat s -> scope s
  VEnumOrTag sc _ _ -> sc
  VWildcard sc -> sc
  VSyntaxCat sc _ -> sc
  VNeutral s -> scope s
  VUniverse sc -> sc
  VPi s (n , t) -> scope s 

expand' :: forall a. WithSyntaxCat a -> SyntaxTable -> HeadUpData' ActorMeta -> ASemanticsDesc -> Maybe (VSemanticsDesc' a)
expand' w table dat desc = do
  go True (headUp dat desc) where

  go :: Bool -> ASemanticsDesc -> Maybe (VSemanticsDesc' a)  
  go b s = ($ s) (asAtomOrTagged (goAtoms b) (goTagged b s))
       <|> pure (VNeutral desc)

  goAtoms b (a, sc) = case a of
    "Atom" -> pure $ VAtom sc
    "Nil"  -> pure $ VNil sc
    "Wildcard" -> pure $ VWildcard sc
    "Semantics" -> pure $ VUniverse sc
    a -> do
      s <- Map.lookup a table
      case w of
        Yes -> pure (VSyntaxCat sc a)
        No -> do guard b
                 go False (embed s)

  goTagged b s (a, sc) = case a of
    "AtomBar" -> asPair $ asListOf (asAtom $ Just . fst)
                        $ \ xs _ -> pure (VAtomBar sc xs)
    "Cons" -> asPair $ \ s0 -> asPair $ \ s1 _ -> pure (VCons s0 s1)
    "NilOrCons" -> asPair $ \ s0 -> asPair $ \ s1 _ -> pure (VNilOrCons s0 s1)
    "Bind" -> asTagged $ \ (a,_) -> asPair $ \ s _ -> pure (VBind a s)
    "Tag" -> asPair $ \ s0 s1 -> goTagged b s ("EnumOrTag", sc) (nil sc % s0 % s1)
    "Enum" -> asPair $ \ s0 s1 -> goTagged b s ("EnumOrTag", sc) (s0 % nil sc % s1)
    "EnumOrTag" -> asPair $ \ es -> asPair $ \ ts _ ->
                     ($ es) $ asListOf (asAtom $ Just . fst) $ \ xs ->
                     ($ ts) $ asListOf (asTagged $ \ (a, _) -> asList $ \ bs -> Just (a, bs)) $ \ ys ->
                     pure (VEnumOrTag sc xs ys)
    "Fix" -> asPair $ asBind $ \ x s' _ -> go False (s' //^ topSbst x s)
    "Pi" -> asPair $ \ s0 -> asPair $ asBind $ \ x s1 _ -> pure $ VPi s0 (x, s1)
    _ -> bust

expand :: SyntaxTable -> HeadUpData' ActorMeta -> ASemanticsDesc -> Maybe VSemanticsDesc
expand = expand' No

contract' :: WithSyntaxCat a -> VSemanticsDesc' a -> ASemanticsDesc
contract' w = \case
  VAtom sc -> atom "Atom" sc
  VAtomBar sc xs -> "AtomBar" #%+ [enums sc (\ s -> atom s sc) xs]
  VNil sc -> atom "Nil" sc
  VCons s t -> "Cons" #%+ [s, t]
  VNilOrCons s t -> "NilOrCons" #%+ [s, t]
  VBind cat s -> "Bind" #%+ [catToDesc cat, s]
  VEnumOrTag sc es ts -> "EnumOrTag" #%+
    [enums sc (\ s -> atom s sc) es, enums sc ( \ (t, s) -> (t,0) #% s) ts]
  VWildcard sc -> atom "Wildcard" sc
  VSyntaxCat sc cat -> case w of
    Yes -> atom cat sc
    No -> absurd cat
  VNeutral s -> s
  VUniverse sc -> atom "Semantics" sc
  VPi s (n , t) -> "Pi" #%+ [s, n \\ t]
  where
    enums sc f= foldr (%) (nil sc) . map f

contract :: VSemanticsDesc -> ASemanticsDesc
contract = contract' No


catToDesc :: SyntaxCat -> ASemanticsDesc
catToDesc c = atom c 0

validate :: Show m => SyntaxTable -> Bwd SyntaxCat -> ASemanticsDesc -> CdB (Tm m) -> Bool
validate table = _
{-
  go :: Show m => Bwd SyntaxCat -> ASemanticsDesc -> CdB (Tm m) -> Bool
  go env s t@(CdB V th) = reportError s t $ ($ s) $ asRec $ \ a -> a == env <! (dbIndex $ lsb th)
  go env s t = reportError s t $ ($ t) $ flip (maybe bust) (expand table s) $ \case
    VAtom _ -> asAtom $ \ (a,_) -> not (null a)
    VAtomBar _ as -> asAtom $ \ (a,_) -> not (a `elem` as)
    VNil _ -> asAtom $ \ (a,_) -> null a
    VCons s0 s1 -> asPair $ \ t0 t1 -> go env s0 t0 && go env s1 t1
    VNilOrCons s0 s1 -> asNilOrCons True $ \ t0 t1 -> go env s0 t0 && go env s1 t1
    VBind a s -> asBind $ \ x t -> go (env :< a) s t
    VEnumOrTag _ es ds -> asAtomOrTagged (\ (e,_) -> e `elem` es)
                                       (\ (a,_) t -> case lookup a ds of
                                           Nothing -> False
                                           Just ss -> gos env ss t)
    VWildcard _ -> \ _ -> True

  reportError :: Show m => ASemanticsDesc -> CdB (Tm m) -> Bool -> Bool
  reportError d t True = True
  reportError d t False = False -- error $ "Validation error\nDesc: " ++ show d ++ "\nTerm: " ++ show t

  gos :: Show m => Bwd SyntaxCat -> [ASemanticsDesc] -> CdB (Tm m) -> Bool
  gos env [] = asNil True
  gos env (s:ss) = asPair $ \ t0 t1 -> go env s t0 && gos env ss t1
-}
  
typecheck :: SyntaxTable
          -> Bwd SyntaxCat          -- already known syntax environment
          -> HeadUpData' ActorMeta 
          -> Bwd ASemanticsDesc     -- type context `ctx`
          -> ASemanticsDesc         -- type `ty` we are checking, `ty` lives in `ctx`
          -> ACTm                   -- term `t` we are checking, `t` is alson in `ctx`
          -> Bool
typecheck table env dat = check where
  check :: Bwd ASemanticsDesc -> ASemanticsDesc -> ACTm -> Bool
  check ctx ty t = let (Just vty) = expand table dat ty in case Term.expand t of
    _ | VWildcard _ <- vty -> True
    VX v sc -> ty == var ctx sc v -- should maybe be up to unfolding (which might be undecidable)
    AX a sc -> case vty of
      VAtom _ -> True
      VAtomBar _ as -> a `notElem` as
      VNil _ -> a == ""
      VNilOrCons{} -> a == ""
      VEnumOrTag _ es _ -> a `elem` es
      VUniverse _ -> a `elem` (env :< "Semantics")
      VBind{} -> False
      VCons{} -> False
      VSyntaxCat{} -> False
      VNeutral{} -> False
      VPi{} -> False
    a0 :%: a1 -> case vty of
      VNilOrCons ty0 ty1 -> check ctx ty0 a0 && check ctx ty1 a1 
      VEnumOrTag _ _ atys -> ($ a0) $ asAtom $ \(a, _) -> case lookup a atys of
          Nothing -> False
          Just tys -> checks ctx tys a1
      VUniverse sc -> ($ a0) $ asAtom $ \(s, _) ->  (&&) (s == "Pi")
        $ ($ a1) $ asPair $ \ty0 -> asPair $ \ty1 -> asNil
          $ check ctx (universe sc) ty0 && check (ctx :< ty0) (universe $ sc + 1)  ty1 
      VCons ty0 ty1 -> check ctx ty0 a0 && check ctx ty1 a1
      _ -> False  -- don't forget to handle any new cases
    a0 :-: a1 -> _ 
    _ :.: t0 -> case vty of
      VBind cat ty0 -> check (ctx :< atom cat (scope t)) ty0 t0
      VPi ty0 (_, ty1) -> check (ctx :< ty0) ty1 t0
      _ -> False
    m :$: t0 -> _
    GX _ t0 -> check ctx ty t0


  checks :: Bwd ASemanticsDesc -> [ASemanticsDesc] -> ACTm -> Bool
  checks ctx [] t = ($ t) $ asNil True
  checks ctx (ty : tys) t = ($ t) $ asPair $ \t0 t1 -> check ctx ty t0 && checks ctx tys t1
  
  var :: Bwd ASemanticsDesc -> Int -> DB -> ASemanticsDesc
  var ctx sc (DB i) = (ctx <! i) *^ (ones (sc - (1 + i)) <> none (1 + i))

  universe sc = contract $ VUniverse sc
      
listOf :: String -> ASemanticsDesc -> ASemanticsDesc
listOf x d = let ga = scope d + 1 in
  "Fix" #%+ [x \\ (atom "NilOrCons" ga % (weak d % var (DB 0) ga % nil ga))]

{-
rec :: String -> ASemanticsDesc
rec a = atom a 0

syntaxDesc :: [SyntaxCat] -> ASemanticsDesc
syntaxDesc syns = "EnumOrTag" #%+ [
  enums (atoms ++ syns),
  (atom "AtomBar" 0 % (listOf "at" atom0 % nil 0)) %
  (atom "Cons" 0 % (syntax % syntax % nil 0)) %
  (atom "NilOrCons" 0 % (syntax % syntax % nil 0)) %
  (atom "Bind" 0 % (("EnumOrTag" #%+ [enums syns, nil 0]) % syntax % nil 0)) %
  (atom "EnumOrTag" 0 % (listOf "at" atom0
                       % listOf "cell" (atom "Cons" 0 % atom0 % (listOf "rec" syntax % nil 0)) % nil 0)) %
  (atom "Enum" 0 % listOf "at" atom0 % nil 0) %
  (atom "Tag" 0 % (listOf "cell" (atom "Cons" 0 % atom0 % (listOf "rec" syntax % nil 0)) % nil 0)) %
  (atom "Fix" 0 % ("Bind" #%+ [atom "Syntax" 0, syntax]) % nil 0) %
  nil 0]
  where syntax = rec "Syntax"
        atom0 = atom "Atom" 0 -- ("Atom",0) #% []
        atoms = ["Nil", "Atom", "Wildcard"]
        enums sc = foldr (%) (nil 0) $ map (\ s -> atom s 0) sc


{- > printIt

['EnumOrTag
  ['Nil 'Atom 'Wildcard 'Syntax]
  [['AtomBar ['Fix (\list.['NilOrCons 'Atom list])]]
   ['Cons 'Syntax 'Syntax]
   ['NilOrCons 'Syntax 'Syntax]
   ['Bind ['EnumOrTag ['Syntax] []] 'Syntax]
   ['EnumOrTag ['Fix (\list.['NilOrCons 'Atom list])]
               ['Fix (\list.['NilOrCons ['Cons 'Atom ['Fix (\list.['NilOrCons 'Syntax list])]] list])]]
   ['Enum ['Fix (\list.['NilOrCons 'Atom list])]]
   ['Tag ['Fix (\list.['NilOrCons ['Cons 'Atom ['Fix (\list.['NilOrCons 'Syntax list])]] list])]]
   ['Fix ['Bind 'Syntax 'Syntax]]]]

-}

validateDesc :: [SyntaxCat] -> ASemanticsDesc -> Bool
validateDesc syns =
    validate (Map.fromList known) B0
     (rec "Syntax")
  where
     known = [ ("Syntax", syntaxDesc syns)
             , ("Semantics", wildcard)] -- TODO : change


validateIt = validateDesc ["Syntax"] (syntaxDesc ["Syntax"])
-}
