module Impl.TAC.Pass.MappingTree

import Impl.TAC.TAC
import Impl.TAC.Data
import Impl.TAC.Pass.Common

import Data.List

data Core = P1 | P2

Eq Core where
  P1 == P1 = True
  P2 == P2 = True
  _ == _   = False

data Mapped a = MapTo a Core

getContent: Mapped a -> a
getContent (MapTo x y) = x

getCore: Mapped a -> Core
getCore (MapTo x y) = y

data EvalTree: Type where
  Var  : (label: Nat)  -> (onCore: Core) -> EvalTree
  State: (label: Nat) -> (onCore: Core) -> EvalTree
  Const: EvalTree
  Op: (lable: Nat) -> (deps: List EvalTree) 
   -> (onCore: Core) -> EvalTree
  
lookupMapped: Eq a => a -> List (Mapped a) -> Maybe Core
lookupMapped x xs = 
  case filter (\y => getContent y == x) xs of 
    [res] => Just $ getCore res
    _ => Nothing

dataToTree: FTACData -> Core -> EvalTree
dataToTree (SVar label _) core = Var label core
dataToTree x core = Const

findDef': FTACData -> (List $ Mapped FlatOp) 
  -> Maybe (Mapped FlatOp)
findDef' x xs = 
  let res = 
        filter 
          (\(op `MapTo` _) => getDst op == x)
          xs
  in case res of 
       [res] => Just res
       _ => Nothing -- should be only one definition

getLabel: FTACData -> Maybe Nat
getLabel (SVar label _) = Just label
getLabel x = Nothing

mkTree: (inputs : List $ Mapped FTACData)
  -> (states : List $ Mapped FlatSt)
  -> (outputs: List $ Mapped FTACData)
  -> (ops    : List $ Mapped FlatOp)
  -> (root   : Mapped FlatOp)
  -> Maybe EvalTree
mkTree inputs states outputs ops  ((st@(MkSt vSt) ::= val) `MapTo` _) = 
  do core    <- lookupMapped st states
     label   <- getLabel vSt
     subtree <- genSubtree
     pure $ Op label [subtree] core
where 
  genSubtree : Maybe EvalTree
  genSubtree = 
    case lookupMapped val inputs of
      (Just core') => Just $ dataToTree val core'
      Nothing => 
        case findDef' val ops of
          Nothing => Nothing
          (Just x) => mkTree inputs states outputs ops x
mkTree inputs states outputs ops  ((val <<= st@(MkSt vSt)) `MapTo` core) = 
  do stCore   <- lookupMapped st states
     label    <- getLabel val
     stLabel  <- getLabel vSt
     let mkTrOn = Op label [State stLabel stCore]
         core' = 
           case lookupMapped val outputs of 
             Nothing =>  core
             (Just outCore) => outCore
     pure $ mkTrOn core'
mkTree inputs states outputs ops  (op `MapTo` core) = 
  let srcs = getSrc op
      dst  = getDst op
  in do label <- getLabel dst 
        subtrees <- swap $ map genSubtree srcs
        pure $ Op label subtrees core
where
  genSubtree: FTACData -> Maybe EvalTree
  genSubtree val = 
    case lookupMapped val inputs of
      Nothing => 
        case findDef' val ops of
          Nothing => Nothing
          (Just x) => mkTree inputs states outputs ops x
      (Just x) => Just $ dataToTree val x
      
  swap: List (Maybe a) -> Maybe (List a)
  swap = foldr (\x, xs => [| x :: xs|])  (Just [])
  
genEvalTree: (inputMap: List Core) 
  -> (outputMap: List Core)
  -> (stateMap : List Core)
  -> (opsMap   : List Core)
  -> (op: Mapped FlatOp)
  -> FTAC -> Maybe EvalTree
genEvalTree inputMap outputMap stateMap opsMap op
            (MkFTAC input output state ops) = 
  let m: (forall a. List a -> _) = zipWith (\x, y => x `MapTo` y) 
      input'  = m input inputMap
      output' = m output outputMap
      state'  = m state stateMap
      ops'    = m ops opsMap
  in mkTree input' state' output' ops' op

mkVar: Nat -> FTACData
mkVar x = SVar x $ BvTy 8
      
testTAC: FTAC
testTAC = 
  MkFTAC [mkVar 0] 
         [mkVar 1] 
         [MkSt $ mkVar 2]
         [(mkVar 3) <<= MkSt (mkVar 2),
          ADD  (mkVar 0) (mkVar 3) (mkVar 4),
          ADD  (mkVar 4) (mkVar 3) (mkVar 5),
          MULT (mkVar 4) (mkVar 3) (mkVar 6),
          ADD  (mkVar 4) (mkVar 6) (mkVar 1),
          MkSt (mkVar 2) ::= (mkVar 1)]

  
testTree: Maybe EvalTree
testTree = genEvalTree [P1] [P1] [P1] [P1, P1, P1, P2, P1, P1] (MULT (mkVar 4) (mkVar 3) (mkVar 6) `MapTo` P2) testTAC



