module Impl.TAC.Types

import Data.Signal
import Data.BitVec

public export
data Name = Anon | NM String

public export
data TACTy: Type where
  BvTy  : (width: Nat) -> TACTy
  ProdTy: (a: TACTy) -> (b: TACTy) -> TACTy
  UnitTy: TACTy
  
%name TACTy ty1, ty2

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
data TACData: Type where
  Const: {n: _} -> BitVec n -> TACData
  U    : TACData
  Var  : (nm: Name) -> TACTy -> TACData
  
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
  (==) (Var nm1 ty1) (Var nm2 ty2) = 
    (nm1 == nm2) && (ty1 == ty2)
  (==) _ _ = False

public export
getTy: TACData -> TACTy
getTy (Const {n} x) = BvTy n
getTy U             = UnitTy
getTy (Var nm ty1)  = ty1

export infixr 9 ::=
export infixr 9 ~>

public export
data TACGl1: Type where
  PROD   : TACData -> TACData -> (dst: TACData) -> TACGl1
  PROJ1  : TACData -> (dst: TACData) -> TACGl1
  PROJ2  : TACData -> (dst: TACData) -> TACGl1

public export
data TACOp1: Type where
  (::=)  : TACData -> TACData -> TACOp1 -- assignment
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
