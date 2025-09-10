module Impl.TAC.FlatTAC

import Data.Signal
import Data.BitVec
import Data.Linear
import Data.State

import Impl.TAC.TAC

public export
data FTACData: Type where
  Const: {n: _} -> BitVec n -> FTACData
  U    : FTACData
  SVar : (label: Nat) -> TACTy -> FTACData -- simple variable

public export
getTy: FTACData -> TACTy
getTy (Const {n} x)  = BvTy n
getTy U              = UnitTy
getTy (SVar _ ty1)   = ty1
      
public export
Eq FTACData where
  (==) (Const {n=n1} x) (Const {n=n2} y) with (cmp n1 n2)
    (==) (Const {n=n1} x) (Const {n=n1} y) | CmpEQ = x == y
    (==) (Const {n=n1} x) (Const {n=n2} y) | _     = False
  (==) U U = True
  (==) (SVar label1 ty1) (SVar label2 ty2) = 
    (label1 == label2) && (ty1 == ty2)
  (==) _ _ = False

export infixr 9 ::=
export infixr 9 <<=

public export
data FTACSt: Type where
  MkSt: FTACData -> FTACSt

public export
data FTACOp1: Type where
  (::=)  : (st: FTACSt) -> (src: FTACData) -> FTACOp1
  (<<=)  : (dst: FTACData) -> (st: FTACSt) -> FTACOp1
  ADD    : (src1: FTACData) -> (src2: FTACData) -> (dst: FTACData) -> FTACOp1
  CONCAT : (src1: FTACData) -> (src2: FTACData) -> (dst: FTACData) -> FTACOp1
  AND    : (src1: FTACData) -> (src2: FTACData) -> (dst: FTACData) -> FTACOp1
  OR     : (src1: FTACData) -> (src2: FTACData) -> (dst: FTACData) -> FTACOp1
  XOR    : (src1: FTACData) -> (src2: FTACData) -> (dst: FTACData) -> FTACOp1
  EQ     : (src1: FTACData) -> (src2: FTACData) -> (dst: FTACData) -> FTACOp1
  LTU    : (src1: FTACData) -> (src2: FTACData) -> (dst: FTACData) -> FTACOp1
  LT     : (src1: FTACData) -> (src2: FTACData) -> (dst: FTACData) -> FTACOp1
  MUX21  : (src1: FTACData) -> (src2: FTACData) -> (src3: FTACData) 
        -> (dst:  FTACData) -> FTACOp1
  SLL    : Nat -> (src: FTACData) -> (dst: FTACData) -> FTACOp1
  SRL    : Nat -> (src: FTACData) -> (dst: FTACData) -> FTACOp1
  SRA    : Nat -> (src: FTACData) -> (dst: FTACData) -> FTACOp1
  NOT    : (src: FTACData) -> (dst: FTACData) -> FTACOp1
  SLICE  : Nat -> Nat -> (src: FTACData) -> (dst: FTACData) -> FTACOp1
  MULT   : (src1: FTACData) -> (src2: FTACData) -> (dst: FTACData) -> FTACOp1

export
mapOperands: (FTACData -> FTACData) -> FTACOp1 -> FTACOp1
mapOperands f (st ::= src)               = st ::= f src
mapOperands f (dst <<= st)               = f dst <<= st
mapOperands f (ADD src1 src2 dst)        = ADD (f src1) (f src2) (f dst)       
mapOperands f (CONCAT src1 src2 dst)     = CONCAT (f src1) (f src2) (f dst)    
mapOperands f (AND src1 src2 dst)        = AND (f src1) (f src2) (f dst)       
mapOperands f (OR src1 src2 dst)         = OR (f src1) (f src2) (f dst)        
mapOperands f (XOR src1 src2 dst)        = XOR (f src1) (f src2) (f dst)       
mapOperands f (EQ src1 src2 dst)         = EQ (f src1) (f src2) (f dst)        
mapOperands f (LTU src1 src2 dst)        = LTU (f src1) (f src2) (f dst)       
mapOperands f (LT src1 src2 dst)         = LT (f src1) (f src2) (f dst)        
mapOperands f (MUX21 src1 src2 src3 dst) = MUX21 (f src1) (f src2) (f src3) (f dst)
mapOperands f (SLL k src dst)            = SLL k (f src) (f dst)           
mapOperands f (SRL k src dst)            = SRL k (f src) (f dst)           
mapOperands f (SRA k src dst)            = SRA k (f src) (f dst)           
mapOperands f (NOT src dst)              = NOT (f src) (f dst)             
mapOperands f (SLICE k j src dst)        = SLICE k j (f src) (f dst)
mapOperands f (MULT src1 src2 dst)       = MULT (f src1) (f src2) (f dst)

public export
record FTAC1 where
  constructor MkTAC1
  input : List FTACData
  output: List FTACData
  state : List FTACSt
  ops   : List FTACOp1
