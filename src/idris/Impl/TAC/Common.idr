module Impl.TAC.Common

import Impl.TAC.TAC

import Data.Signal
import Data.State
import Data.BitVec

public export
proj1Ty: TACTy -> TACTy
proj1Ty (ProdTy a b) = a
proj1Ty _ = believe_me "impossible"

public export
proj2Ty: TACTy -> TACTy
proj2Ty (ProdTy a b) = b
proj2Ty _ = believe_me "impossible"

public export
fromSig: Sig a -> TACTy
fromSig U = UnitTy
fromSig (P x y) = 
  ProdTy (fromSig x) (fromSig y)
fromSig (BV {n}) = BvTy n

public export
fromSt: St s -> TACTy
fromSt LU = UnitTy
fromSt (LP st1 st2) = 
  ProdTy (fromSt st1) (fromSt st2)
fromSt (LV {n}) = BvTy n

export
flatData: (old: TACData) -> (new: TACData) -> List (TACData, TACData)
flatData (CVar d11 d12 ty1) (CVar d21 d22 ty2) = 
  (flatData d11 d21) ++ (flatData d12 d22)
flatData old new = [(old, new)]

export
--x[old => new]
substData'': (old: TACData) -> (new: TACData) 
        -> TACData -> TACData
substData'' old new x = 
  if x == old then new 
  else case x of
         (CVar d1 d2 ty1) => 
           let d1' = substData'' old new d1
               ty1 = getTy d1'
               d2' = substData'' old new d2
               ty2 = getTy d2'
           in CVar d1' d2' $ ProdTy ty1 ty2
         _ => x

substData': List (TACData, TACData)
         -> TACData -> TACData
substData' [] x = x
substData' ((old, new) :: xs) x = 
  let x' = substData'' old new x
  in substData' xs x'

export
substData: (old: TACData) -> (new: TACData) 
        -> TACData -> TACData
substData old new x = 
  substData' (flatData old new) x

substOp1: (old: TACData) -> (new: TACData) 
       -> TACOp1 -> TACOp1
substOp1 old new x = 
  mapOperands (substData old new) x

export
substTAC1: (old: TACData) -> (new: TACData) 
        -> TAC1 -> TAC1
substTAC1 old new tac = 
  let subst = substData old new 
      substOps: List _ -> _ 
        = (map $ substOp1 old new)
  in {input $= subst, output $= subst, ops $= substOps} tac
  
public export
interface Op op dat where
  getSrc: op -> List dat
  getDst: op -> dat

public export
Op TACOp1 TACData where
  getSrc = getUsed
  getDst = TAC.getDst

public export
findDef: TACData -> List TACOp1 -> Maybe TACOp1
findDef x [] = Nothing
findDef x (y :: xs) = 
  if getDst y == x then Just y 
  else findDef x xs
