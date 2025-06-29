module Impl.Eval.Seq

import Impl.Eval.Eval
import Impl.Eval.Comb

import Sym.Comb.Comb
import Sym.Seq.Seq

import Data.LState
import Data.Signal
import Data.State

public export
Seq Combinational Sequential where
  abst f = MkSeq 
    $ \x => let x' = MkComb (\y:Unit => x) 
            in runSeq (f x') ()
  
  (=<<) (MkSeq g) (MkSeq f) = MkSeq (g =<< f)
  
  pure (MkComb f) = MkSeq $ \x => pure $ f x
  
  (<<<) (MkSeq g) (MkSeq f) = MkSeq (LState.(<<<) g f)
  
  swap (MkSeq f) = MkSeq $ \xin => LST $ \(st2 # st1) => 
    let LST f' = (f xin) 
        (st1 # st2) # o = f' (st1 # st2)
     in (st2 # st1) # o
  
