module Impl.TAC.Comb.Comb

import Impl.TAC.Common
import Impl.TAC.TAC
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
              let in' = MkTAC1 U var []
              res <- genTACC $ f (MkTACC $ pure in')
              pure $ {input := var} res
  
  app (MkTACC f) (MkTACC x)  = 
    MkTACC $ 
      do x <- x
         f <- f
         let f' = substTAC1 f.input x.output f
         pure $ MkTAC1 U f'.output (x.ops ++ f'.ops)
                
  prod (MkTACC x) (MkTACC y) = 
    MkTACC $ 
      do x <- x
         y <- y
         pure 
           $ MkTAC1 U (prodData x.output y.output) 
               $ x.ops ++ y.ops
                   
  proj1 (MkTACC x) = 
    MkTACC $ 
      do x <- x
         pure $ {output $= proj1Data} x
                
  proj2 (MkTACC x) = 
    MkTACC $ 
      do x <- x
         pure $ {output $= proj2Data} x
  
  unit = MkTACC $ ST $ \c => Id (c, MkTAC1 U U [])

