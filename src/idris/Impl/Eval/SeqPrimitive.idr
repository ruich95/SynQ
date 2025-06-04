module Impl.Eval.SeqPrimitive

import Impl.Eval.Eval
import Impl.Eval.Comb
import Impl.Eval.Seq

import Sym.Comb.Comb
import Sym.Seq.Seq
import Sym.Seq.SeqPrimitive


import Data.LState
import Data.State
import Data.BitVec
import Data.Signal

import Data.Linear

public export
Seq Combinational Sequential => Reg a Combinational Sequential where
  get = MkSeq 
    $ \() => LST 
      $ \st => let (MkBang st'): (!* a) = stToSig st 
               in (sigToSt st') # st'
  set (MkComb x) = 
    let st: s = sigToSt $ x () 
    in MkSeq $ \() => LST 
      (\1 y => let () = stConsume y 
               in st # ())

public export
reg: (Seq Combinational Sequential) => Reg a Combinational Sequential
reg = MkReg get set
where
  get: {auto aIsSig: Sig a} -> {auto sIsState: St s}
    -> {auto similar: SameShape a s}
    -> Sequential s () a
  get = MkSeq 
    $ \() => LST 
      $ \st => let (MkBang st'): (!* a) = stToSig st 
               in (sigToSt st') # st'
               
  set: {auto aIsSig: Sig a} -> {auto sIsState: St s}
      -> {auto similar: SameShape a s}
      -> Combinational () a -> Sequential s () ()          
  set (MkComb x) = 
    let st: s = sigToSt $ x () 
    in MkSeq $ \() => LST 
      (\1 y => let () = stConsume y 
               in st # ())
