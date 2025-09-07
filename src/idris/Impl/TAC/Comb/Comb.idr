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
              res <- genTacC $ f (MkTACC $ pure in')
              pure $ {input := var} res
  
  app (MkTACC f) (MkTACC x)  = 
    MkTACC $ 
      do (MkTAC1 _  outX opsX) <- x
         f <- f
         let (MkTAC1 _ outY opsY) = substInput1 f outX
         pure $ MkTAC1 U outY (opsX ++ opsY)
                
  prod (MkTACC x) (MkTACC y) = 
    MkTACC $ 
      do (MkTAC1 _ outX opsX) <- x
         (MkTAC1 _ outY opsY) <- y
         let outXTy = getTy outX
             outYTy = getTy outY
             outTy  = ProdTy outXTy outYTy
         outVar <- genVar outTy
         let prodOp: TACAtom1 = Gl $ PROD outX outY outVar
         pure $ MkTAC1 U outVar $ opsX ++ opsY ++ [prodOp]
                   
  proj1 (MkTACC x) = 
    MkTACC $ 
      do (MkTAC1 _ outX opsX) <- x
         let outXTy = getTy outX
             outTy  = proj1Ty outXTy
         outVar <- genVar outTy
         let proj1Op: TACAtom1 = Gl $ PROJ1 outX outVar
         pure $ MkTAC1 U outVar $ snoc opsX proj1Op
                
  proj2 (MkTACC x) = 
    MkTACC $ 
      do (MkTAC1 _ outX opsX) <- x
         let outXTy = getTy outX
             outTy  = proj2Ty outXTy
         outVar <- genVar outTy
         let proj2Op: TACAtom1 = Gl $ PROJ2 outX outVar
         pure $ MkTAC1 U outVar $ snoc opsX proj2Op
  
  unit = MkTACC $ ST $ \c => Id (c, MkTAC1 U U [])

