module Impl.TAC.Comb.CombPrimitive

import Impl.TAC.Common
import Impl.TAC.TAC
import Impl.TAC.GenTAC

import Sym.Comb.CombPrimitive

import Data.Signal
import Data.BitVec 
import Data.List

import Control.Monad.State

public export
Primitive TACComb where
  const x = 
    MkTACC $ ST $ \c => Id (c, MkTAC1 U (Const x) [])
  
  add (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy $ S n)
      let op = Op $ ADD outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
                                   
  concat (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy $ m + n)
      let op = Op $ CONCAT outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
  
  not (MkTACC x) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      dst <- genVar (BvTy n)
      let op = Op $ NOT outX dst
      pure $ MkTAC1 U dst 
                    (opsX ++ [op])
    
  and (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy n)
      let op = Op $ AND outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
  
  or (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy n)
      let op = Op $ OR outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
  
  xor (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy n)
      let op = Op $ XOR outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
  
         
  slice lower upper (MkTACC x) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      dst <- genVar (BvTy $ upper `minus` lower)
      let op = Op $ SLICE lower upper outX dst
      pure $ MkTAC1 U dst 
                    (opsX ++ [op])
  
  eq (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy 1)
      let op = Op $ EQ outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
  
  ltu (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy 1)
      let op = Op $ LTU outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
                                   
  lt (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy 1)
      let op = Op $ LT outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
                                   
  mux21 (MkTACC b) (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outB opsB) <- b
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy n)
      let op = Op $ MUX21 outB outX outY dst
      pure $ MkTAC1 U dst 
                    (opsB ++ opsX ++ opsY ++ [op])
                                       
  shiftLL sht (MkTACC x) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      dst <- genVar (BvTy n)
      let op = Op $ SLL sht outX dst
      pure $ MkTAC1 U dst 
                    (opsX ++ [op])

  shiftRL sht (MkTACC x) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      dst <- genVar (BvTy n)
      let op = Op $ SRL sht outX dst
      pure $ MkTAC1 U dst 
                    (opsX ++ [op])
    
  shiftRA sht (MkTACC x) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      dst <- genVar (BvTy n)
      let op = Op $ SRA sht outX dst
      pure $ MkTAC1 U dst 
                    (opsX ++ [op])

