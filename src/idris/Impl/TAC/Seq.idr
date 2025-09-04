module Impl.TAC.Seq

import Sym.Comb.Comb
import Sym.Seq.Seq

import Control.Monad.State

import Data.LState
import Data.Signal
import Data.State

import Data.Linear
import Data.List
import Data.LC 

import Impl.TAC.TAC

import Impl.TAC.Types
import Impl.TAC.Comb

public export
Seq TACComb TACSeq where
  abst f = ?rhs1
  
  pure (MkTACC f) = ?rhs2
       
  (=<<) (MkTACS g) (MkTACS f) = 
    MkTACS $ do g <- g 
                
                ?rhs
  
  (<<<) (MkTACS g) (MkTACS f) = ?rhs4
                
  swap (MkTACS f) = ?rhs5
