module Impl.TAC.TAC

import Data.Signal
import Data.BitVec
import Data.Linear
import Data.State

public export
data Name = Anon | NM String

public export
data TACTy: Type where
  BvTy  : (width: Nat) -> TACTy
  ProdTy: (a: TACTy) -> (b: TACTy) -> TACTy
  UnitTy: TACTy
  
%name TACTy ty1, ty2

public export
data TACData: Type where
  Const: {n: _} -> BitVec n -> TACData
  U    : TACData
  SVar : (label: Nat) -> TACTy -> TACData -- simple variable
  CVar : (d1: TACData) -> (d2: TACData) 
      -> TACTy -> TACData -- product of variables

public export
getTy: TACData -> TACTy
getTy (Const {n} x)  = BvTy n
getTy U              = UnitTy
getTy (SVar _ ty1)   = ty1
getTy (CVar _ _ ty1) = ty1

public export
prodData: TACData -> TACData -> TACData
prodData x y = CVar x y (ProdTy (getTy x) (getTy y))

public export
proj1Data: TACData -> TACData
proj1Data (CVar d1 d2 ty1) = d1
proj1Data _ = believe_me "impossible"

public export
proj2Data: TACData -> TACData
proj2Data (CVar d1 d2 ty1) = d2
proj2Data _ = believe_me "impossible"

public export
Eq Name where
  (==) Anon Anon = True
  (==) (NM str1) (NM str2) = str1 == str2
  (==) _ _ = False

public export
Eq TACTy where
  (==) (BvTy width1) (BvTy width2) = 
    width1 == width2
  (==) (ProdTy a1 b1) (ProdTy a2 b2) = 
    (a1 == a2) && (b1 == b2)
  (==) UnitTy UnitTy = True
  (==) _ _ = False
      
public export
Eq TACData where
  (==) (Const {n=n1} x) (Const {n=n2} y) with (cmp n1 n2)
    (==) (Const {n=n1} x) (Const {n=n1} y) | CmpEQ = x == y
    (==) (Const {n=n1} x) (Const {n=n2} y) | _     = False
  (==) U U = True
  (==) (SVar label1 ty1) (SVar label2 ty2) = 
    (label1 == label2) && (ty1 == ty2)
  (==) (CVar d11 d12 ty1) (CVar d21 d22 ty2) = 
    (d11 == d21) && (d12 == d22) && (ty1 == ty2)
  (==) _ _ = False

export infixr 9 ::=
export infixr 9 <<=

public export
data TACSt: Type where
  MkSt: TACData -> TACSt
  
public export
splitSt: TACSt -> (TACSt, TACSt)
splitSt (MkSt (CVar d1 d2 ty1)) = (MkSt d1, MkSt d2)
splitSt _ = believe_me "impossible"

public export
prodSt: TACSt -> TACSt -> TACSt
prodSt (MkSt x) (MkSt y) = MkSt (prodData x y)

public export
data TACOp1: Type where
  (::=)  : (st: TACSt) -> (src: TACData) -> TACOp1
  (<<=)  : (dst: TACData) -> (st: TACSt) -> TACOp1
  ADD    : (src1: TACData) -> (src2: TACData) -> (dst: TACData) -> TACOp1
  CONCAT : (src1: TACData) -> (src2: TACData) -> (dst: TACData) -> TACOp1
  AND    : (src1: TACData) -> (src2: TACData) -> (dst: TACData) -> TACOp1
  OR     : (src1: TACData) -> (src2: TACData) -> (dst: TACData) -> TACOp1
  XOR    : (src1: TACData) -> (src2: TACData) -> (dst: TACData) -> TACOp1
  EQ     : (src1: TACData) -> (src2: TACData) -> (dst: TACData) -> TACOp1
  LTU    : (src1: TACData) -> (src2: TACData) -> (dst: TACData) -> TACOp1
  LT     : (src1: TACData) -> (src2: TACData) -> (dst: TACData) -> TACOp1
  MUX21  : (src1: TACData) -> (src2: TACData) -> (src3: TACData) 
        -> (dst:  TACData) -> TACOp1
  SLL    : Nat -> (src: TACData) -> (dst: TACData) -> TACOp1
  SRL    : Nat -> (src: TACData) -> (dst: TACData) -> TACOp1
  SRA    : Nat -> (src: TACData) -> (dst: TACData) -> TACOp1
  NOT    : (src: TACData) -> (dst: TACData) -> TACOp1
  SLICE  : Nat -> Nat -> (src: TACData) -> (dst: TACData) -> TACOp1
  MULT   : (src1: TACData) -> (src2: TACData) -> (dst: TACData) -> TACOp1

export
mapOperands: (TACData -> TACData) -> TACOp1 -> TACOp1
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
record TAC1 where
  constructor MkTAC1
  input : TACData
  output: TACData
  ops   : List TACOp1
  
