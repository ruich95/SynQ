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
  
eval: MTAC -> History
eval x = fst $ runState init (evalToEnd x)

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
          AND  (mkVar 4) (mkVar 3) (mkVar 7),
          ADD  (mkVar 7) (mkVar 6) (mkVar 1),
          MkSt (mkVar 2) ::= (mkVar 1)]


testMapping: Mapping
testMapping = MkMapping [P1] [P1] [P1] [P1, P1, P1, P2, P2, P1, P1]

testMTAC: MTAC
testMTAC = mapFTAC testTAC testMapping

-- testTree: Maybe EvalTree
-- testTree = genEvalTree [P1] [P1] [P1] [P1, P1, P1, P2, P1, P1] (MULT (mkVar 4) (mkVar 3) (mkVar 6) `MapTo` P2) testTAC




