module Impl.TAC.Pass.StateMove

import Impl.TAC.TAC
import Impl.TAC.Data
import Impl.TAC.Pass.Common
import Data.List

record StOps where
  constructor MkStOps
  getOps: List FlatOp
  setOps: List FlatOp

moveStateStep: StOps -> Zipper FlatOp
  -> (StOps, Zipper FlatOp)
moveStateStep x z@(MkZipper prev (Just op) rest) = 
  case isGet op of
    Nothing => 
      case isSet op of
        Nothing => (x, next z)
        (Just (st, src)) => 
          let x' = {setOps $= \t => snoc t (st ::= src)} x
          in (x', next $ drop z)
    (Just (dst, st)) => 
      let x' = {getOps $= \t => snoc t (dst <<= st)} x
      in (x', next $ drop z)
moveStateStep x z = (x, next z)

moveState': StOps -> Zipper FlatOp
  -> (StOps, Zipper FlatOp)
moveState' x z1 = 
  if isEnd z1 then moveStateStep x z1 
  else let (x', z') = moveStateStep x z1 
       in moveState' x' z'
       

export
moveState2: FTAC -> FTAC2
moveState2 (MkFTAC input output state ops) = 
  let ops = fromList ops 
      (MkStOps getOps setOps, ops) = 
        moveState' (MkStOps [] []) ops
      ops = Common.toList ops
  in (MkFTAC2 input output state getOps ops setOps)
                     
export
moveState: FTAC -> FTAC
moveState tac = 
  toFTAC $ moveState2 tac

