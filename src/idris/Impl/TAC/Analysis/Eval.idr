module Impl.TAC.Analysis.Eval

import Impl.TAC.Data
import Impl.TAC.TAC

import Data.List
import Control.Monad.State

public export
isElement: (Eq a) => a -> List a -> Bool
isElement x [] = False
isElement x (y :: xs) = 
  if x == y then True 
  else isElement x xs

public export
FlatOp: Type
FlatOp = TACOp FTACData 

public export
FlatSt: Type
FlatSt = TACSt FTACData

public export
isGet: FlatOp -> Maybe (FTACData, FlatSt)
isGet (dst <<= st) = Just (dst, st)
isGet _ = Nothing

public export
isSet: FlatOp -> Maybe (FlatSt, FTACData)
isSet (st ::= src) = Just (st, src)
isSet _ = Nothing

export
notIn: Eq a => a -> List a -> Bool
notIn x [] = True
notIn x (y :: xs) = if x == y then False 
                    else notIn x xs

data Core = P1 | P2

Eq Core where
  P1 == P1 = True
  P2 == P2 = True
  _ == _ = False

data Mapped a = MapTo a Core

mapTo: List a -> List Core -> List (Mapped a)
mapTo = zipWith (\x, y => MapTo x y)

record Mapping where
  constructor MkMapping
  input : List Core
  output: List Core
  state : List Core
  ops   : List Core
  
record MTAC where
  constructor MkMTAC
  input : List $ Mapped FTACData
  output: List $ Mapped FTACData 
  state : List $ Mapped FlatSt
  p1Ops : List FlatOp
  p2Ops : List FlatOp
  
mapFTAC: FTAC -> Mapping -> MTAC
mapFTAC x y = 
  MkMTAC (mapTo x.input  y.input) 
         (mapTo x.output y.output)
         (mapTo x.state  y.state)
         (map fst 
            $ filter (\x => snd x == P1) 
            $ zip x.ops y.ops)
         (map fst 
            $ filter (\x => snd x == P2) 
            $ zip x.ops y.ops)

record History where
  constructor Remeber
  onP1 : List FTACData
  onP2 : List FTACData
  steps: Nat
  comms: Nat

lookupInHistory: FTACData 
  -> History -> (Maybe Core, Maybe Core)
lookupInHistory x y = 
  let onP1 = if isElement x y.onP1 
             then Just P1 else Nothing
      onP2 = if isElement x y.onP2 
             then Just P2 else Nothing
  in (onP1, onP2)

lookup': Eq a => a -> List (Mapped a) -> Maybe Core
lookup' x xs = 
  case filter (\(x' `MapTo` _) => x == x') xs of 
    [(_ `MapTo` c)] => Just c
    _ => Nothing

lookupInInput: FTACData -> MTAC -> Maybe Core
lookupInInput x y = lookup' x y.input

lookupInOutput: FTACData -> MTAC -> Maybe Core
lookupInOutput x y = lookup' x y.output

isEnd: MTAC -> Bool
isEnd x = (x.p1Ops == [])
       && (x.p2Ops == [])

canEval: FlatOp -> Core 
  -> (ctx: (MTAC, History)) 
  -> Maybe $ List Core
canEval op core ctx = 
  let deps = getSrc op 
  in ?canEval_rhs

eval: MTAC -> State History MTAC
eval tac with (isEnd tac)
  eval tac | False = ?eval_rhs_0_rhs_0
  eval tac | True  = 
    ST $ \s => Id (s, tac)
