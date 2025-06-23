module Impl.Compile.SeqPrimitive

import Impl.Compile.Compile
import Impl.Compile.Comb
import Impl.Compile.Seq

import Language.Reflection

import Sym.Comb
-- import Sym.CombPrimitive
-- import Sym.SeqPrimitive
import Sym.Seq

import Data.Linear
import Data.LState
import Data.State
import Data.LC
import Data.Signal
import Data.State
import Data.BitVec

%hide SeqLib.(>>=)

public export
Seq Combinational Sequential => Reg a Combinational Sequential where
  get = MkSeq $ lambda _ $ \_ => 
          pure $ LST $ \st => 
            let (MkBang x) = stToSig st {similar=similar} 
            in (sigToSt x # x)
                       
  set (MkComb x) = MkSeq $ do x  <- x <*> pure ()
                              st <- pure $ sigToSt x {similar= similar}
                              lambda _ $ \_ => 
                                pure $ LST $ \st' => 
                                  let () = stConsume st' 
                                  in (st # ())

public export
reg: (Seq Combinational Sequential) => {0 b:_} -> Reg b Combinational Sequential
reg {b} = MkReg get set
where
  get: {auto aIsSig: Sig b} -> {auto sIsState: St s}
    -> {auto similar: SameShape b s}
    -> Sequential s () b
  get = MkSeq $ pure 
              $ \u => LST 
              $ \st => let (MkBang st'): (!* b) = stToSig st 
                       in (sigToSt st') # st'
               
  set: {auto aIsSig: Sig b} -> {auto sIsState: St s}
      -> {auto similar: SameShape b s}
      -> Combinational () b -> Sequential s () ()          
  set (MkComb x) = MkSeq $ do x  <- x <*> pure ()
                              st <- pure $ sigToSt x {similar= similar}
                              lambda _ $ \_ => 
                                pure $ LST $ \st' => 
                                  let () = stConsume st' 
                                  in (st # ())
                              
    -- let toSt: b -> s = \y => sigToSt y 
    --     st: Elab s = [| toSt (x <*> pure ()) |]
    -- in MkSeq $ (pure $ \y => \u => LST 
    --                  $ \st' => let () = stConsume st' 
    --                            in (y # ()))
    --            <*> st
               
