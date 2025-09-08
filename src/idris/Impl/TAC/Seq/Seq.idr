module Impl.TAC.Seq.Seq

import Sym.Comb.Comb
import Sym.Seq.Seq

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
Seq TACComb TACSeq where
  abst f = MkTACS 
    $ LST $ \(MkBang c) => 
       let (c', varIn) = 
             runState c $ genVar $ fromSig aIsSig
           input = MkTACC $ pure $ MkTAC1 U varIn []
           (MkTACS $ LST f) = f input
           (c'' # f') = f (MkBang c')
       in c'' # \st => {input := varIn} $ f' st
  
  pure (MkTACC f) = 
    MkTACS $ LST 
      $ \(MkBang c) => 
          let (c', f) = runState c f
          in (MkBang c') # \_ => f
       
  (=<<) (MkTACS g) (MkTACS f) = 
    MkTACS $ do f <- f 
                g <- g
                pure $ \st => 
                  let f'  = f st
                      g'  = g st
                      g'' = substTAC1 g'.input f'.output g'
                  in MkTAC1 f'.input g''.output 
                            (f'.ops ++ g''.ops)
  
  (<<<) (MkTACS g) (MkTACS f) = 
    MkTACS $ do f <- f 
                g <- g
                pure $ \st => 
                  let (st1, st2) = splitSt st
                      f'  = f st1
                      g'  = g st2
                      g'' = substTAC1 g'.input f'.output g'
                  in MkTAC1 f'.input g''.output 
                            (f'.ops ++ g''.ops)
                
  swap (MkTACS f) = 
    MkTACS $ do f <- f
                pure $ \st => 
                  let (st1, st2) = splitSt st 
                      st' = prodSt st2 st1 
                  in f st'
