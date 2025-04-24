module Sym.Seq.SeqPrimitive

import Data.Signal
import Data.State

import Sym.Comb

%hide Data.Linear.Interface.seq

public export
interface Comb comb 
  => Reg (comb: Type -> Type -> Type)
         (seq: Type -> Type -> Type -> Type) | seq where
  constructor MkReg
  1 get: {auto aIsSig: Sig a} -> {auto sIsState: St s}
      -> {auto similar: SameShape a s}
      -> seq s () a
   
  1 set: {auto aIsSig: Sig a} -> {auto sIsState: St s}
      -> {auto similar: SameShape a s}
      -> comb () a -> seq s () ()
