module Impl.TAC.Seq.SeqPrimitive

import Sym.Comb.Comb
import Sym.Seq.SeqPrimitive

import Control.Monad.State

import Data.LState
import Data.Signal
import Data.State

import Data.Linear
import Data.List
import Data.LC 

import Impl.TAC.Common
import Impl.TAC.TAC
import Impl.TAC.GenTAC
import Impl.TAC.Comb

public export                                   
reg: Reg a TACComb TACSeq
reg = MkReg get set
where
  get: {auto aIsSig: Sig a} -> {auto sIsState: St s}
    -> {auto similar: SameShape a s}
    -> TACSeq s () a
  get = MkTACS $ LST 
      $ \(MkBang c # (MkSt nm ty)) => 
           (MkBang c # MkSt nm ty) 
         # (MkTAC1 U (Var nm ty) [])
                                     
  set: {auto aIsSig: Sig a} -> {auto sIsState: St s}
    -> {auto similar: SameShape a s}
    -> TACComb () a -> TACSeq s () ()
  set (MkTACC x) = MkTACS $ LST 
                 $ \(MkBang c # (MkSt name ty)) => 
                     let (c', (MkTAC1 _ outX opsX)) = runState c x
                     in (MkBang c' # MkSt name ty) 
                      # (MkTAC1 U U 
                           $ opsX 
                           ++ [Op $ Var name ty ::= outX])
