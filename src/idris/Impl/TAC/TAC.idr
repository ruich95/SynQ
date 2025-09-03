module Impl.TAC.TAC

import Impl.TAC.Types
import Control.Monad.State

public export
record TACComb (a: Type) (b: Type) where
  constructor MkTACC
  genTacC: State Nat TAC1
  
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
  in x' ::= y
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
genVar: TACTy -> State Nat TACData
genVar ty = ST $ \c => Id (S c, Var (NM "x_\{show c}") ty)
