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

public export
getTy: TACData -> TACTy
getTy (Const {n} x)  = BvTy n
getTy U              = UnitTy
getTy (SVar _ ty1)   = ty1
getTy (CVar _ _ ty1) = ty1

export infixr 9 ::=

public export
data TACGl1: Type where
  PROD   : TACData -> TACData -> (dst: TACData) -> TACGl1
  PROJ1  : TACData -> (dst: TACData) -> TACGl1
  PROJ2  : TACData -> (dst: TACData) -> TACGl1

public export
data TACOp1: Type where
  (::=)  : TACData -> TACData -> TACOp1 -- set state
  ADD    : TACData -> TACData -> (dst: TACData) -> TACOp1
  CONCAT : TACData -> TACData -> (dst: TACData) -> TACOp1
  AND    : TACData -> TACData -> (dst: TACData) -> TACOp1
  OR     : TACData -> TACData -> (dst: TACData) -> TACOp1
  XOR    : TACData -> TACData -> (dst: TACData) -> TACOp1
  EQ     : TACData -> TACData -> (dst: TACData) -> TACOp1
  LTU    : TACData -> TACData -> (dst: TACData) -> TACOp1
  LT     : TACData -> TACData -> (dst: TACData) -> TACOp1
  MUX21  : TACData -> TACData -> TACData -> (dst: TACData) -> TACOp1
  SLL    : Nat     -> TACData -> (dst: TACData) -> TACOp1
  SRL    : Nat     -> TACData -> (dst: TACData) -> TACOp1
  SRA    : Nat     -> TACData -> (dst: TACData) -> TACOp1
  NOT    : TACData -> (dst: TACData) -> TACOp1
  SLICE  : Nat -> Nat -> TACData -> (dst: TACData) -> TACOp1

public export
data TACAtom1 = Gl TACGl1 | Op TACOp1

public export
record TAC1 where
  constructor MkTAC1
  input : TACData
  output: TACData
  ops   : List TACAtom1

public export
data TACSt: Type where
  MkSt: (name: Name) -> (ty: TACTy) -> TACSt
  
public export
data TACGl2: Type where
  IDX: TACData -> (idx: Nat) -> (dst: TACData) -> TACGl2

public export
data TACAtom2 = Gl2 TACGl2 | Op2 TACOp1

public export
record TAC2 where
  constructor MkTAC2
  input : TACData
  output: TACData
  ops   : List TACAtom2
      
-- public export
-- record TAC2 where
--   constructor MkTAC2
--   get  : TACSt -> TACData 
--   1 set  : TACData -> TACSt
