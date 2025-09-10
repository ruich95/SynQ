module Impl.TAC.Pass.GetEliminate

import Impl.TAC.TAC
import Impl.TAC.Data
import Impl.TAC.Pass.Common

isGet: TACOp FTACData 
  -> Maybe (TACSt FTACData)
isGet (_ <<= st) = Just st
isGet _ = Nothing

isSet: TACOp FTACData -> Bool
isSet (_ ::= _) = True
isSet _ = False

findEarly: TACSt FTACData 
  -> List (TACOp FTACData)
  -> Maybe FTACData
findEarly x [] = Nothing
findEarly x (y :: xs) = 
  case isGet y of
       Nothing => findEarly x xs
       (Just z) => if x == z 
                   then (Just $ getDst y) 
                   else findEarly x xs

getElim1Step: Zipper (TACOp FTACData) 
  -> Zipper (TACOp FTACData)
getElim1Step z@(MkZipper prev (Just x) rest) = 
  case isGet x of 
    Nothing => next z
    (Just y) => 
      let earlyDst = findEarly y prev
      in case earlyDst of
           Nothing => next z
           (Just dst') =>
             let updateFn: (List _ -> _) = 
                   map $ \op => substOp 
                                (getDst x) 
                                dst' op
             in next $ drop $ {rest $= updateFn} z
getElim1Step z = next z

getElim1: Zipper (TACOp FTACData) 
  -> Zipper (TACOp FTACData)
-- getElim1 (MkZipper prev (Just x) rest) = ?getElim1_rhs_2
getElim1 z = if isEnd z then getElim1Step z 
             else getElim1 $ getElim1Step z 
