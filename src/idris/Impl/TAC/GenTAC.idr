module Impl.TAC.GenTAC

import Impl.TAC.TAC
import Impl.TAC.Common

import Control.Monad.State
import Data.LState
import Data.Linear
import Data.State

public export
record TACComb (a: Type) (b: Type) where
  constructor MkTACC
  genTACC: State Nat TAC1

public export
data TACSeq: Type -> Type -> Type -> Type where
  MkTACS: (1 _: LState (!* Nat) $ TACSt -> TAC1) -> TACSeq _ _ _
  
public export
genTACS: (1 _: TACSeq s a b) 
  -> LState (!* Nat) $ TACSt -> TAC1
genTACS (MkTACS x) = x

public export
genVar: TACTy -> State Nat TACData
genVar (ProdTy a b) = 
  do v1 <- genVar a 
     v2 <- genVar b 
     pure $ prodData v1 v2
genVar ty = ST $ \c => Id (S c, SVar c ty)

public export
genTAC: {auto sIsSt: St s} 
  -> (1 _: TACSeq s a b) 
  -> (TACSt, TAC1)
genTAC (MkTACS f) = 
  let (MkBang c # f') 
        = LState.runState f (MkBang 0)
      (_ , stv) = runState c (genVar $ fromSt sIsSt)
      st = MkSt stv
  in (st, f' st)
