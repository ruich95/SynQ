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

--x[old => new]
substData: (old: TACData) -> (new: TACData) 
        -> TACData -> TACData
substData old new x = 
  if x == old then new 
  else case x of
         (CVar d1 d2 ty1) => 
           let d1' = substData old new d1
               ty1 = getTy d1'
               d2' = substData old new d2
               ty2 = getTy d2'
           in CVar d1' d2' $ ProdTy ty1 ty2
         _ => x
  
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
getUsed: TACOp1 -> List TACData
getUsed (x ::= y)         = [y]
getUsed (ADD x y dst)     = [x, y]
getUsed (CONCAT x y dst)  = [x, y]
getUsed (AND x y dst)     = [x, y]
getUsed (OR x y dst)      = [x, y]
getUsed (XOR x y dst)     = [x, y]
getUsed (EQ x y dst)      = [x, y]
getUsed (LTU x y dst)     = [x, y]
getUsed (LT x y dst)      = [x, y]
getUsed (MUX21 x y z dst) = [x, y, z]
getUsed (SLL k x dst)     = [x]
getUsed (SRL k x dst)     = [x]
getUsed (SRA k x dst)     = [x]
getUsed (NOT x dst)       = [x]
getUsed (SLICE k j x dst) = [x]

public export
getDst: TACOp1 -> TACData
getDst ((MkSt x) ::= y)  = x
getDst (ADD x y dst)     = dst
getDst (CONCAT x y dst)  = dst
getDst (AND x y dst)     = dst
getDst (OR x y dst)      = dst
getDst (XOR x y dst)     = dst
getDst (EQ x y dst)      = dst
getDst (LTU x y dst)     = dst
getDst (LT x y dst)      = dst
getDst (MUX21 x y z dst) = dst
getDst (SLL k x dst)     = dst
getDst (SRL k x dst)     = dst
getDst (SRA k x dst)     = dst
getDst (NOT x dst)       = dst
getDst (SLICE k j x dst) = dst

public export
findDef: TACData -> List TACOp1 -> Maybe TACOp1
findDef x [] = Nothing
findDef x (y :: xs) = 
  if getDst y == x then Just y 
  else findDef x xs
