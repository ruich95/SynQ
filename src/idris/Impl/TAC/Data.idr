module Impl.TAC.Data

import Data.BitVec
import Data.Signal
import Data.State

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
interface Typed a where
  getTy: a -> TACTy
  
export
Typed TACData where
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

substData: (old: TACData) -> (new: TACData) 
        -> TACData -> TACData
substData old new x = 
  substData' (flatData old new) x
  
public export
interface Subst a where
  --x[old => new]
  subst: (old: a) -> (new: a) -> (x: a) -> a

public export
Subst TACData where
  subst = substData

export
Show TACTy where
  show (BvTy width) = 
    "BV \{show width}"
  show (ProdTy a b) = 
    "(\{show a}, \{show b})"
  show UnitTy = "()"

ppData: (p: String) -> TACData -> String
ppData _ (Const x) = "\{show x}"
ppData _ U = "()"
ppData p (SVar label ty1) = 
  "\{p}_\{show label}"
ppData p (CVar d1 d2 ty1) = 
  "(\{ppData p d1}, \{ppData p d2})"

export
Show TACData where
  show x = 
    let ty = getTy x 
    in "\{ppData "x" x}: \{show ty}"

namespace Flatted 
  public export
  data FTACData: Type where
    Const: {n: _} -> BitVec n -> FTACData
    U    : FTACData
    SVar : (label: Nat) -> TACTy -> FTACData -- simple variable

  public export
  Eq FTACData where
    (==) (Const {n=n1} x) (Const {n=n2} y) with (cmp n1 n2)
      (==) (Const {n=n1} x) (Const {n=n1} y) | CmpEQ = x == y
      (==) (Const {n=n1} x) (Const {n=n2} y) | _     = False
    (==) U U = True
    (==) (SVar label1 ty1) (SVar label2 ty2) = 
      (label1 == label2) && (ty1 == ty2)
    (==) _ _ = False
  
  export
  Typed FTACData where
    getTy (Const {n} x)  = BvTy n
    getTy U              = UnitTy
    getTy (SVar _ ty1)   = ty1
    
  ppData: (p: String) -> FTACData -> String
  ppData _ (Const x) = "\{show x}"
  ppData _ U = "()"
  ppData p (SVar label ty1) = 
    "\{p}_\{show label}"
  
  export
  Show FTACData where
    show x = 
      let ty = getTy x 
      in "\{ppData "x" x}: \{show ty}"
      
  export
  Subst FTACData where
    subst old new x = 
      if old == x then new else x
    
