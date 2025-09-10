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

import Impl.TAC.Data
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
          $ \(MkBang c) => 
               let (c', var) = 
                     runState c (genVar $ fromSig aIsSig)
               in MkBang c' 
                # \st => MkTAC U var st [var <<= st]
                                     
  set: {auto aIsSig: Sig a} -> {auto sIsState: St s}
    -> {auto similar: SameShape a s}
    -> TACComb () a -> TACSeq s () ()
  set (MkTACC f) = 
    MkTACS $ LST $ \(MkBang c) => 
      let (c', f') = runState c f 
      in MkBang c' 
       # \st => let op = st ::= f'.output
                in MkTAC U U st (snoc f'.ops op)
