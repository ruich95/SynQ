module Impl.TAC.Pass.Partition

import Impl.TAC.TAC
import Impl.TAC.Data
import Impl.TAC.Pass.Common

import Data.SortedMap
import Control.Monad.State

data OpNode: Type where
  INPUT  : OpNode
  OUTPUT : OpNode
  SET    : (label: Int) -> OpNode
  GET    : (label: Int) -> OpNode
  ADD    : (label: Int) -> OpNode
  CONCAT : (label: Int) -> OpNode
  AND    : (label: Int) -> OpNode
  OR     : (label: Int) -> OpNode
  XOR    : (label: Int) -> OpNode
  EQ     : (label: Int) -> OpNode
  LTU    : (label: Int) -> OpNode
  LT     : (label: Int) -> OpNode
  MUX21  : (label: Int) -> OpNode
  SLL    : (label: Int) -> OpNode
  SRL    : (label: Int) -> OpNode
  SRA    : (label: Int) -> OpNode
  NOT    : (label: Int) -> OpNode
  SLICE  : (label: Int) -> OpNode
  MULT   : (label: Int) -> OpNode
  
opTypeToInt: OpNode -> Int
opTypeToInt (SET label)    = 0
opTypeToInt (GET label)    = 1
opTypeToInt (ADD label)    = 2
opTypeToInt (CONCAT label) = 3
opTypeToInt (AND label)    = 4
opTypeToInt (OR label)     = 5
opTypeToInt (XOR label)    = 6
opTypeToInt (EQ label)     = 7
opTypeToInt (LTU label)    = 8
opTypeToInt (LT label)     = 9
opTypeToInt (MUX21 label)  = 10
opTypeToInt (SLL label)    = 11
opTypeToInt (SRL label)    = 12
opTypeToInt (SRA label)    = 13
opTypeToInt (NOT label)    = 14
opTypeToInt (SLICE label)  = 15
opTypeToInt (MULT label)   = 16
opTypeToInt INPUT  = 17
opTypeToInt OUTPUT = 18

getLabel: OpNode -> Int
getLabel (SET label)    = label
getLabel (GET label)    = label
getLabel (ADD label)    = label
getLabel (CONCAT label) = label
getLabel (AND label)    = label
getLabel (OR label)     = label
getLabel (XOR label)    = label
getLabel (EQ label)     = label
getLabel (LTU label)    = label
getLabel (LT label)     = label
getLabel (MUX21 label)  = label
getLabel (SLL label)    = label
getLabel (SRL label)    = label
getLabel (SRA label)    = label
getLabel (NOT label)    = label
getLabel (SLICE label)  = label
getLabel (MULT label)   = label
getLabel INPUT  = 0
getLabel OUTPUT = 0


Eq OpNode where
  (==) x y = 
    let nx = opTypeToInt x 
        ny = opTypeToInt y
    in if nx == ny then getLabel x == getLabel y
       else False

Ord OpNode where
  (<) x y = 
    let nx = opTypeToInt x 
        ny = opTypeToInt y
    in if nx == ny then False
       else getLabel x < getLabel y

Graph: Type
Graph = SortedMap OpNode (List OpNode)

mapToNode': FlatOp -> State Int (FlatOp, OpNode)
mapToNode' x@(_ ::= _)       = ST $ \c => Id (c+1, (x, SET c))
mapToNode' x@(_ <<= _)       = ST $ \c => Id (c+1, (x, GET c))
mapToNode' x@(ADD _ _ _)     = ST $ \c => Id (c+1, (x, ADD c))
mapToNode' x@(CONCAT _ _ _)  = ST $ \c => Id (c+1, (x, CONCAT c))
mapToNode' x@(AND _ _ _)     = ST $ \c => Id (c+1, (x, AND c))
mapToNode' x@(OR _ _ _)      = ST $ \c => Id (c+1, (x, OR c))
mapToNode' x@(XOR _ _ _)     = ST $ \c => Id (c+1, (x, XOR c))
mapToNode' x@(EQ _ _ _)      = ST $ \c => Id (c+1, (x, EQ c))
mapToNode' x@(LTU _ _ _)     = ST $ \c => Id (c+1, (x, LTU c))
mapToNode' x@(LT _ _ _)      = ST $ \c => Id (c+1, (x, LT c))
mapToNode' x@(MUX21 _ _ _ _) = ST $ \c => Id (c+1, (x, MUX21 c))
mapToNode' x@(SLL _ _ _)     = ST $ \c => Id (c+1, (x, SLL c))
mapToNode' x@(SRL _ _ _)     = ST $ \c => Id (c+1, (x, SRL c))
mapToNode' x@(SRA _ _ _)     = ST $ \c => Id (c+1, (x, SRA c))
mapToNode' x@(NOT _ _)       = ST $ \c => Id (c+1, (x, NOT c))
mapToNode' x@(SLICE _ _ _ _) = ST $ \c => Id (c+1, (x, SLICE c))
mapToNode' x@(MULT _ _ _)    = ST $ \c => Id (c+1, (x, MULT c))

mapToNode'': List FlatOp -> State Int $ List (FlatOp, OpNode)
mapToNode'' [] = pure []
mapToNode'' (x :: xs) = 
  do x <- mapToNode' x
     rest <- mapToNode'' xs
     pure $ x :: rest
     
mapToNode: List FlatOp -> List (FlatOp, OpNode)
mapToNode xs = snd $ runState 0 (mapToNode'' xs)

lookup: List (FlatOp, OpNode) -> FlatOp -> Maybe OpNode
lookup [] x = Nothing
lookup (y :: xs) x = if (fst y) == x then Just (snd y) else lookup xs x
