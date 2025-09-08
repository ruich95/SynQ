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
      let op = ADD outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
                                   
  concat (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy $ m + n)
      let op = CONCAT outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
  
  not (MkTACC x) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      dst <- genVar (BvTy n)
      let op = NOT outX dst
      pure $ MkTAC1 U dst 
                    (opsX ++ [op])
    
  and (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy n)
      let op = AND outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
  
  or (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy n)
      let op = OR outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
  
  xor (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy n)
      let op = XOR outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
  
         
  slice lower upper (MkTACC x) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      dst <- genVar (BvTy $ upper `minus` lower)
      let op = SLICE lower upper outX dst
      pure $ MkTAC1 U dst 
                    (opsX ++ [op])
  
  eq (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy 1)
      let op = EQ outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
  
  ltu (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy 1)
      let op = LTU outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
                                   
  lt (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy 1)
      let op = LT outX outY dst
      pure $ MkTAC1 U dst 
                    (opsX ++ opsY ++ [op])
                                   
  mux21 (MkTACC b) (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC1 _ outB opsB) <- b
      (MkTAC1 _ outX opsX) <- x
      (MkTAC1 _ outY opsY) <- y
      dst <- genVar (BvTy n)
      let op = MUX21 outB outX outY dst
      pure $ MkTAC1 U dst 
                    (opsB ++ opsX ++ opsY ++ [op])
                                       
  shiftLL sht (MkTACC x) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      dst <- genVar (BvTy n)
      let op = SLL sht outX dst
      pure $ MkTAC1 U dst 
                    (opsX ++ [op])

  shiftRL sht (MkTACC x) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      dst <- genVar (BvTy n)
      let op = SRL sht outX dst
      pure $ MkTAC1 U dst 
                    (opsX ++ [op])
    
  shiftRA sht (MkTACC x) = 
    MkTACC $ do 
      (MkTAC1 _ outX opsX) <- x
      dst <- genVar (BvTy n)
      let op = SRA sht outX dst
      pure $ MkTAC1 U dst 
                    (opsX ++ [op])

