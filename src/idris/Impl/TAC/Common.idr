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

public export
substByGl1: (old: TACData) -> (new: TACData) -> TACGl1 -> TACGl1
substByGl1 old new (PROD z w dst) = 
  let z'   = if z == old   then new else z 
      w'   = if w == old   then new else w
      dst' = if dst == old then new else dst
  in PROD z' w' dst'
substByGl1 old new (PROJ1 z dst) = 
  let z'   = if z == old   then new else z 
      dst' = if dst == old then new else dst
  in PROJ1 z' dst'
substByGl1 old new (PROJ2 z dst) = 
  let z'   = if z == old   then new else z 
      dst' = if dst == old then new else dst
  in PROJ2 z' dst'


substByOp1: (old: TACData) -> (new: TACData) -> TACOp1 -> TACOp1
substByOp1 old new (x ::= y) = 
  let x'   = if x == old   then new else x
      y'   = if y == old   then new else y
  in x' ::= y'
substByOp1 old new (x <<= y) = 
  let x'   = if x == old   then new else x
      y'   = if y == old   then new else y
  in x' <<= y'
substByOp1 old new (ADD x y dst) = 
  let x'   = if x == old   then new else x
      y'   = if y == old   then new else y
      dst' = if dst == old then new else dst
  in ADD x' y' dst'
substByOp1 old new (CONCAT x y dst) = 
  let x'   = if x == old   then new else x
      y'   = if y == old   then new else y
      dst' = if dst == old then new else dst
  in CONCAT x' y' dst'
substByOp1 old new (AND x y dst) = 
  let x'   = if x == old   then new else x
      y'   = if y == old   then new else y
      dst' = if dst == old then new else dst
  in AND x' y' dst'
substByOp1 old new (OR x y dst) = 
  let x'   = if x == old   then new else x
      y'   = if y == old   then new else y
      dst' = if dst == old then new else dst
  in OR x' y' dst'
substByOp1 old new (XOR x y dst) = 
  let x'   = if x == old   then new else x
      y'   = if y == old   then new else y
      dst' = if dst == old then new else dst
  in XOR x' y' dst'
substByOp1 old new (EQ x y dst) = 
  let x'   = if x == old   then new else x
      y'   = if y == old   then new else y
      dst' = if dst == old then new else dst
  in EQ x' y' dst'
substByOp1 old new (LTU x y dst) = 
  let x'   = if x == old   then new else x
      y'   = if y == old   then new else y
      dst' = if dst == old then new else dst
  in LTU x' y' dst'
substByOp1 old new (LT x y dst) = 
  let x'   = if x == old   then new else x
      y'   = if y == old   then new else y
      dst' = if dst == old then new else dst
  in LT x' y' dst'
substByOp1 old new (MUX21 b x y dst) = 
  let b'   = if b == old   then new else b
      x'   = if x == old   then new else x
      y'   = if y == old   then new else y
      dst' = if dst == old then new else dst
  in MUX21 b' x' y' dst'
substByOp1 old new (SLL k x dst) = 
  let x'   = if x == old   then new else x
      dst' = if dst == old then new else dst
  in SLL k x' dst'
substByOp1 old new (SRL k x dst) = 
  let x'   = if x == old   then new else x
      dst' = if dst == old then new else dst
  in SRL k x' dst'
substByOp1 old new (SRA k x dst) = 
  let x'   = if x == old   then new else x
      dst' = if dst == old then new else dst
  in SRA k x' dst'
substByOp1 old new (NOT x dst) = 
  let x'   = if x == old   then new else x
      dst' = if dst == old then new else dst
  in NOT x' dst'
substByOp1 old new (SLICE k j x dst) = 
  let x'   = if x == old   then new else x
      dst' = if dst == old then new else dst
  in SLICE k j x' dst'

public export
substBy1: (old: TACData) -> (new: TACData) 
  -> List TACAtom1 -> List TACAtom1
substBy1 old new [] = []
substBy1 old new ((Gl x) :: xs) = 
  (Gl $ substByGl1 old new x) :: (substBy1 old new xs)
substBy1 old new ((Op x) :: xs) = 
  (Op $ substByOp1 old new x) :: (substBy1 old new xs)

public export
substInput1: TAC1 -> TACData -> TAC1
substInput1 (MkTAC1 input output ops) x = 
  let ops' = substBy1 input x ops 
      output' = if output == x
                then x else output
  in MkTAC1 U output' ops'

public export
getUsed: TACAtom1 -> List TACData
getUsed (Gl (PROD x y dst))    = [x, y]
getUsed (Gl (PROJ1 x dst))     = [x]
getUsed (Gl (PROJ2 x dst))     = [x]
getUsed (Op (x ::= y))         = [y]
getUsed (Op (x <<= y))         = [y]
getUsed (Op (ADD x y dst))     = [x, y]
getUsed (Op (CONCAT x y dst))  = [x, y]
getUsed (Op (AND x y dst))     = [x, y]
getUsed (Op (OR x y dst))      = [x, y]
getUsed (Op (XOR x y dst))     = [x, y]
getUsed (Op (EQ x y dst))      = [x, y]
getUsed (Op (LTU x y dst))     = [x, y]
getUsed (Op (LT x y dst))      = [x, y]
getUsed (Op (MUX21 x y z dst)) = [x, y, z]
getUsed (Op (SLL k x dst))     = [x]
getUsed (Op (SRL k x dst))     = [x]
getUsed (Op (SRA k x dst))     = [x]
getUsed (Op (NOT x dst))       = [x]
getUsed (Op (SLICE k j x dst)) = [x]

public export
getDst: TACAtom1 -> TACData
getDst (Gl (PROD x y dst))    = dst
getDst (Gl (PROJ1 x dst))     = dst
getDst (Gl (PROJ2 x dst))     = dst
getDst (Op (x ::= y))         = x
getDst (Op (x <<= y))         = x
getDst (Op (ADD x y dst))     = dst
getDst (Op (CONCAT x y dst))  = dst
getDst (Op (AND x y dst))     = dst
getDst (Op (OR x y dst))      = dst
getDst (Op (XOR x y dst))     = dst
getDst (Op (EQ x y dst))      = dst
getDst (Op (LTU x y dst))     = dst
getDst (Op (LT x y dst))      = dst
getDst (Op (MUX21 x y z dst)) = dst
getDst (Op (SLL k x dst))     = dst
getDst (Op (SRL k x dst))     = dst
getDst (Op (SRA k x dst))     = dst
getDst (Op (NOT x dst))       = dst
getDst (Op (SLICE k j x dst)) = dst

public export
findDef: TACData -> List TACAtom1 -> Maybe TACAtom1
findDef x [] = Nothing
findDef x (y :: xs) = 
  if getDst y == x then Just y 
  else findDef x xs
