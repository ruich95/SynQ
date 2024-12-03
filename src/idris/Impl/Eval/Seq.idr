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
  
  (<<<) (MkSeq g) (MkSeq f) = MkSeq (g <<< f)
  
