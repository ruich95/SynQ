module Impl.Compile.SeqPrimitive

import Impl.Compile.Compile
import Impl.Compile.Comb
import Impl.Compile.Seq

import Language.Reflection

import Sym.Comb
import Sym.CombPrimitive
import Sym.SeqPrimitive
import Sym.Seq

import Data.Linear
import Data.LState
import Data.State
import Data.LC

public export
Seq Combinational Sequential => Reg Combinational Sequential where
  get = MkSeq $ pure 
              $ \u => LST 
              $ \st => let (MkBang st'): (!* a) = stToSig st 
                       in (sigToSt st') # st'
                       
  set (MkComb x) = 
    let toSt: a -> s = \y => sigToSt y 
        st: Elab s = [| toSt (x <*> pure ()) |]
    in MkSeq $ (pure $ \y => \u => LST 
                     $ \st' => let () = stConsume st' 
                               in (y # ()))
               <*> st

public export
reg: (Seq Combinational Sequential) => Reg Combinational Sequential
reg = MkReg get set
where
  get: {auto aIsSig: Sig a} -> {auto sIsState: St s}
    -> {auto similar: SameShape a s}
    -> Sequential s () a
  get = MkSeq $ pure 
              $ \u => LST 
              $ \st => let (MkBang st'): (!* a) = stToSig st 
                       in (sigToSt st') # st'
               
  set: {auto aIsSig: Sig a} -> {auto sIsState: St s}
      -> {auto similar: SameShape a s}
      -> Combinational () a -> Sequential s () ()          
  set (MkComb x) = 
    let toSt: a -> s = \y => sigToSt y 
        st: Elab s = [| toSt (x <*> pure ()) |]
    in MkSeq $ (pure $ \y => \u => LST 
                     $ \st' => let () = stConsume st' 
                               in (y # ()))
               <*> st
               
fn: (Seq Combinational Sequential)
  => Sequential (!* BitVec 8) (BitVec 8) (BitVec 8)
fn = pure (lam id)

%language ElabReflection

test: (BitVec 8) -> LState (!* BitVec 8) (BitVec 8)
test = %runElab genSeq (fn)
