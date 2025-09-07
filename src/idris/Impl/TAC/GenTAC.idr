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
  genTacC: State Nat TAC1

public export
data TACSeq: Type -> Type -> Type -> Type where
  MkTACS: (1 _: LState (LPair (!* Nat) TACSt) TAC1) -> TACSeq _ _ _
  
public export
genTACS: (1 _: TACSeq s a b) 
  -> LState (LPair (!* Nat) TACSt) TAC1
genTACS (MkTACS x) = x

public export
genTAC: {auto sIsSt: St s} 
  -> (1 _: TACSeq s a b) 
  -> LC TACSt TAC1
genTAC (MkTACS f) = 
  let ty = fromSt sIsSt
      (MkBang _ # st) # sys = 
        LState.runState f (MkBang 0 # MkSt (NM "st") ty)
  in st # sys

public export
genVar: TACTy -> State Nat TACData
genVar ty = ST $ \c => Id (S c, Var (NM "x_\{show c}") ty)
