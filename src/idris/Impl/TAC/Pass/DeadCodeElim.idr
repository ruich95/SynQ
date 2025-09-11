module Impl.TAC.Pass.DeadCodeElim

import Impl.TAC.TAC
import Impl.TAC.Data
import Impl.TAC.Common
import Impl.TAC.Pass.Common

import Data.List
import Data.LC

unusedIn: FTACData -> List FlatOp -> Bool
unusedIn x ops = 
  let srcs = ops >>= getSrc 
  in notIn x srcs
  
elimDeadStep: (List FTACData, Zipper FlatOp) -> (List FTACData, Zipper FlatOp)
elimDeadStep (outs, z@(MkZipper prev (Just x) rest)) = 
  case isSet x of 
    Nothing => 
      let dst = getDst x 
      in if (dst `unusedIn` rest) && (dst `notIn` outs)
         then (outs, next $ drop z)
         else (outs, next z)
    _ => (outs, next z)
elimDeadStep (outs, z) = (outs, next z)


elimDead': (List FTACData, Zipper FlatOp) -> (List FTACData, Zipper FlatOp)
elimDead' z1 = 
  if isEnd $ snd z1 then z1 
  else elimDead' $ elimDeadStep z1
  
export
elimDead: FTAC -> FTAC
elimDead tac@(MkFTAC input output state ops) = 
  let ops' = Common.toList $ snd $ elimDead' (output, fromList ops) 
  in {ops := ops'} tac
