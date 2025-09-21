module Impl.TAC.Analysis.Eval

import Impl.TAC.Data
import Impl.TAC.TAC
import Data.BitVec

import Data.List
import Control.Monad.State

import Language.JSON

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

public export
data Mapped a = MapTo a Core

mapTo: List a -> List Core -> List (Mapped a)
mapTo = zipWith (\x, y => MapTo x y)

public export
record Mapping where
  constructor MkMapping
  input : List Core
  output: List Core
  state : List Core
  ops   : List Core
  
public export
record MTAC where
  constructor MkMTAC
  input : List $ Mapped FTACData
  output: List $ Mapped FTACData 
  state : List $ Mapped FlatSt
  p1Ops : List FlatOp
  p2Ops : List FlatOp

dstIn: FlatOp -> List (Mapped FTACData) -> Maybe Core
dstIn (_::=_) xs = Nothing
dstIn x xs = 
  let dst = getDst x 
  in case filter (\(y `MapTo`_) => y == dst) xs of 
       [(_ `MapTo` core)] => Just core
       _   => Nothing

public export
mapFTAC: FTAC -> Mapping -> MTAC
mapFTAC x y = 
  let mappedOut = (mapTo x.output y.output)
  in MkMTAC (mapTo x.input  y.input) 
            mappedOut  
            (mapTo x.state  y.state)
            (map fst 
               $ filter 
                   (\(op, core) => 
                       case dstIn op mappedOut of
                         Just p => p == P1
                         Nothing => core == P1) 
               $ zip x.ops y.ops)
            (map fst 
               $ filter 
                   (\(op, core) => 
                       case dstIn op mappedOut of
                         Just p => p == P2
                         Nothing => core == P2) 
               $ zip x.ops y.ops)

public export
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

lookupInState: FlatSt -> MTAC -> Maybe Core
lookupInState x y = lookup' x y.state

isEnd: MTAC -> Bool
isEnd x = (x.p1Ops == [])
       && (x.p2Ops == [])

canEval: FlatOp -> Core 
  -> MTAC -> History
  -> Maybe $ List Core
canEval (val <<= st) core tac history = 
  case lookupInState st tac of 
    Nothing => Nothing
    Just c  => Just [c]
canEval op core tac history = 
  let deps = getSrc op 
      cores = map find' deps
  in foldr (\x, xs => [|x :: xs|]) (Just []) cores
where
  find': FTACData -> Maybe Core
  find' (Const _) = Just core -- constants are always avaliable
  find' U = Just core
  find' x = 
    case lookupInHistory x history of
      (Nothing, Nothing) => 
        lookupInInput x tac
      (y, z) => 
        case core of
          P1 => if y == Just P1 
                then Just P1 
                else z
          P2 => if z == Just P2 
                then Just P2
                else y

countComm: Core -> List Core -> Nat
countComm x xs = length $ filter (/= x) xs

eval': MTAC -> State History MTAC
eval' tac = 
  let ops1 = tac.p1Ops 
      ops2 = tac.p2Ops
  in case (ops1, ops2) of
       (op1::ops1, op2::ops2) => 
         ST $ \history => Id 
            $ case (canEval op1 P1 tac history, 
                    canEval op2 P2 tac history) of
                (Nothing, Nothing)    => (history, tac)
                (Nothing, Just cores) => 
                  let moved: List FTACData = 
                        map Builtin.fst 
                          $ filter (\(_, c) => c /= P2) 
                          $ zip (getSrc op2) cores
                  in case op2 of
                       (_ ::= val) => 
                         ({onP2  $= (++) moved,
                           comms $= (+) (countComm P2 cores), 
                           steps $= S} history,
                          {p2Ops := ops2} tac)
                       _ => ({onP2  $= (++) (getDst op2 :: moved), 
                              comms $= (+)  (countComm P2 cores), 
                              steps $= S} history,
                             {p2Ops := ops2} tac)
                (Just cores, Nothing) => 
                  let moved: List FTACData = 
                        map Builtin.fst 
                          $ filter (\(_, c) => c /= P1) 
                          $ zip (getSrc op1) cores
                  in case op1 of
                       (_ ::= val) => 
                         ({onP1  $= (++) moved,
                           comms $= (+) (countComm P1 cores), 
                           steps $= S} history,
                          {p1Ops := ops1} tac)
                       _ => ({onP1  $= (++) (getDst op1 :: moved), 
                              comms $= (+)  (countComm P1 cores), 
                              steps $= S} history,
                             {p1Ops := ops1} tac)
                (Just cs1, Just cs2)  => 
                  let comm1 = countComm P1 cs1 
                      comm2 = countComm P2 cs2
                      comm = comm1 + comm2
                      moved1: List FTACData = 
                        map Builtin.fst 
                          $ filter (\(_, c) => c /= P1) 
                          $ zip (getSrc op1) cs1
                      moved2: List FTACData = 
                        map Builtin.fst 
                          $ filter (\(_, c) => c /= P2) 
                          $ zip (getSrc op2) cs2
                  in case (op1, op2) of
                       (_::=_, _::=_) => 
                         ({onP1  $= (++) moved1,
                           onP2  $= (++) moved2,
                           comms $= (+ comm), 
                           steps $= S} history,
                          {p1Ops := ops1,
                           p2Ops := ops2} tac)
                       (_::=_, y) => 
                         ({onP1  $= (++) moved1,
                           onP2  $= (++) (getDst op2 :: moved2),
                           comms $= (+ comm), 
                           steps $= S} history,
                          {p1Ops := ops1,
                           p2Ops := ops2} tac)
                       (x, _::=_) => 
                         ({onP1  $= (++) (getDst op1 :: moved1),
                           onP2  $= (++) moved2,
                           comms $= (+ comm), 
                           steps $= S} history,
                          {p1Ops := ops1,
                           p2Ops := ops2} tac)
                       (x, y) => 
                         ({onP1  $= (++) (getDst op1 :: moved1),
                           onP2  $= (++) (getDst op2 :: moved2),
                           comms $= (+ comm), 
                           steps $= S} history,
                          {p1Ops := ops1,
                           p2Ops := ops2} tac)
       (op1::ops1, []) => 
         ST $ \history => Id 
            $ case canEval op1 P1 tac history of
                Nothing    => (history, tac)
                Just cores => 
                  let moved: List FTACData = 
                        map Builtin.fst 
                          $ filter (\(_, c) => c /= P1) 
                          $ zip (getSrc op1) cores
                  in case op1 of
                       _ ::= val => 
                         ({onP1  $= (++) moved,
                           comms $= (+) (countComm P1 cores), 
                           steps $= S} history,
                          {p1Ops := ops1} tac)
                       _ => ({onP1  $= (++) (getDst op1 :: moved), 
                              comms $= (+)  (countComm P1 cores), 
                              steps $= S} history,
                             {p1Ops := ops1} tac)
       ([], op2::ops2) => 
         ST $ \history => Id 
            $ case canEval op2 P2 tac history of
                Nothing    => (history, tac)
                Just cores => 
                  let moved: List FTACData = 
                        map Builtin.fst 
                          $ filter (\(_, c) => c /= P2) 
                          $ zip (getSrc op2) cores
                  in case op2 of
                       (_ ::= val) => 
                         ({onP2  $= (++) moved,
                           comms $= (+) (countComm P2 cores), 
                           steps $= S} history,
                          {p2Ops := ops2} tac)
                       _ => ({onP2  $= (++) (getDst op2 :: moved), 
                              comms $= (+)  (countComm P2 cores), 
                              steps $= S} history,
                             {p2Ops := ops2} tac)
       ([], []) => pure tac

init: History
init = Remeber [] [] 0 0

evalToEnd: MTAC -> State History MTAC
evalToEnd tac = 
  if isEnd tac 
  then pure tac
  else (eval' tac) >>= evalToEnd

public export 
eval: MTAC -> History
eval x = fst $ runState init (evalToEnd x)

var: Nat -> FTACData
var x = SVar x $ BvTy 8

cst: Bits64 -> FTACData
cst m = Const $ BV {n=8} m

st: Nat -> FlatSt
st x = MkSt $ var x
                  
testTAC: FTAC
testTAC = 
  MkFTAC [var 0] 
         [var 1] 
         [st 2]
         [(var 3) <<= (st 2),
          ADD  (var 0) (var 3) (var 4),
          ADD  (var 4) (var 3) (var 5),
          MULT (var 4) (var 3) (var 6),
          AND  (var 4) (var 3) (var 7),
          ADD  (var 7) (var 6) (var 1),
          (st 2) ::= (var 1)]


testMapping: Mapping
testMapping = MkMapping [P1] [P2] [P1] [P1, P1, P1, P2, P2, P1, P1]

testMTAC: MTAC
testMTAC = mapFTAC testTAC testMapping

wsum: FTAC
wsum = 
  MkFTAC 
    [var 0] 
    [var 1] 
    [st 2, st 3, st 4] 
    [(var 5) <<= (st 2),
     (var 6) <<= (st 3),
     (var 7) <<= (st 4),
     MULT (var 0)  (cst 1)  (var 8),
     MULT (var 5)  (cst 1)  (var 9),
     MULT (var 6)  (cst 1)  (var 10),
     MULT (var 7)  (cst 1)  (var 11),
     ADD  (var 8)  (var 9)  (var 12),
     ADD  (var 10) (var 11) (var 13),
     ADD  (var 12) (var 13) (var 1),
     (st 2) ::= (var 0),
     (st 3) ::= (var 5),
     (st 4) ::= (var 6)]

wsumMapping: Mapping
wsumMapping = 
  MkMapping 
    [P1] 
    [P1] 
    [P1, P2, P2] 
    [P1, P2, P2, P1, P1, P2, P2, P1, P2, P1, P1, P2, P2]
    
wsumCfg: MTAC
wsumCfg = mapFTAC wsum wsumMapping

json2Core: JSON -> Maybe Core
json2Core (JString "P1") = Just P1
json2Core (JString "P2") = Just P2
json2Core str  = Nothing

swap: List (Maybe a) -> Maybe (List a)
swap [] = Just []
swap (x :: xs) = [| x :: swap xs|]

json2Mapping: JSON -> Maybe Mapping
json2Mapping 
  (JObject 
    [("input" , JArray jInput), 
     ("output", JArray jOutput),
     ("state" , JArray jState),
     ("ops",    JArray jOps)]) = 
  do input  <- swap $ map json2Core jInput
     output <- swap $ map json2Core jOutput
     state  <- swap $ map json2Core jState
     ops    <- swap $ map json2Core jOps
     pure $ MkMapping input output state ops
json2Mapping json = Nothing

export
jStr2Mapping: String -> Maybe Mapping
jStr2Mapping str = 
  do json <- parse str
     json2Mapping json

export
matchedMapping: FTAC -> Mapping -> Bool
matchedMapping x y = 
  (length x.input == length y.input)
  && (length x.output == length y.output) 
  && (length x.state == length y.state) 
  && (length x.ops == length y.ops) -- ?matchedMapping_rhs
