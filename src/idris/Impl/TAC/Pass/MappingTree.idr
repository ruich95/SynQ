module Impl.TAC.Pass.MappingTree

import Impl.TAC.TAC
import Impl.TAC.Data
import Impl.TAC.Pass.Common

import Data.List

data Core = P1 | P2

data Mapped a = MapTo a Core

getContent: Mapped a -> a
getContent (MapTo x y) = x

getCore: Mapped a -> Core
getCore (MapTo x y) = y

data EvalTree: Type where
  Data : (label: Nat)  -> (onCore: Core) -> EvalTree
  State: (label: Nat) -> (onCore: Core) -> EvalTree
  Const: EvalTree
  Op: (lable: Nat) -> (deps: List EvalTree) 
   -> (onCore: Core) -> EvalTree
  
lookupMapped: Eq a => a -> List (Mapped a) -> Maybe (Mapped a)
  
mkTree: (root: Mapped FlatOp)
  -> (ops    : List $ Mapped FlatOp)
  -> (inputs : List $ Mapped FTACData)
  -> (states : List $ Mapped FlatSt)
  -> (outputs: List $ Mapped FTACData)
  -> Maybe EvalTree
mkTree (op `MapTo` core) ops inputs states outputs = 
  case isGet op of
    Nothing => 
      case isSet op of
        Nothing => ?rhs
        Just (dst, st) => 
          case lookupMapped st states of
            Nothing  => Nothing
            Just (MapTo (MkSt $ SVar stLabel _) core') => 
              Just $ Op stLabel [core'] core
            Just (MapTo _ core') => 
              Just $ Op label [Const] core
    Just (SVar label _, st) => 
      case lookupMapped st states of
        Nothing  => Nothing
        Just (MapTo (MkSt $ SVar stLabel _) core') => 
          Just $ Op label [State stLabel core'] core
        Just (MapTo _ core') => 
          Just $ Op label [Const] core
    Just (_, st) => Nothing
    
-- mkTree (core, x) xs = 
--   case getDst x of 
--     SVar label _ => 
--       let srcs = getSrc x
--           defs = zip (map fst xs) 
--                      (map (\y => findDef y 
--                                $ map snd xs) 
--                           srcs)
--           subTrees = zipWith mkTr srcs defs
--       in Op label subTrees core
--     _ => Const
--   where 
--     mkTr: (src: FTACData) 
--        -> (def: (Core, Maybe FlatOp)) -> EvalTree
--     mkTr src (core, Nothing) = 
--       case src of
--         (SVar label ty1) => Data label
--         _ => Const
--     mkTr src (core, Just op) = mkTree (core, op) xs 
 
