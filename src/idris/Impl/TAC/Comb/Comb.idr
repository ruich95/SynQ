module Impl.TAC.Comb.Comb

import Impl.TAC.TAC
import Impl.TAC.Data
import Impl.TAC.GenTAC

import Sym.Comb.Comb

import Data.Signal
import Data.List

import Control.Monad.State

public export
Comb TACComb where
  lam f = 
    let tya = fromSig aIsSig
    in MkTACC 
         $ do var <- genVar tya 
              let in' = MkTAC U var (MkSt U) []
              res <- genTACC $ f (MkTACC $ pure in')
              pure $ {input := var} res
  
  app (MkTACC f) (MkTACC x)  = 
    MkTACC $ 
      do x <- x
         f <- f
         let f' = substTAC f.input x.output f
         pure $ MkTAC U f'.output (MkSt U) (x.ops ++ f'.ops)
                
  prod (MkTACC x) (MkTACC y) = 
    MkTACC $ 
      do x <- x
         y <- y
         pure 
           $ MkTAC U (prodData x.output y.output) (MkSt U)
               $ x.ops ++ y.ops
                   
  proj1 (MkTACC x) = 
    MkTACC $ 
      do x <- x
         pure $ {output $= proj1Data} x
                
  proj2 (MkTACC x) = 
    MkTACC $ 
      do x <- x
         pure $ {output $= proj2Data} x
  
  unit = MkTACC $ ST $ \c => Id (c, MkTAC U U (MkSt U) [])

