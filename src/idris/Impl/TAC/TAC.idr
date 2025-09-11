module Impl.TAC.TAC

import Impl.TAC.Data

import Data.Signal
import Data.State

export infixr 9 ::=
export infixr 9 <<=

public export
data TACSt: Type -> Type where
  MkSt: datTy -> TACSt datTy
  
public export
splitSt: TACSt TACData -> (TACSt TACData, TACSt TACData)
splitSt (MkSt (CVar d1 d2 ty1)) = (MkSt d1, MkSt d2)
splitSt _ = believe_me "impossible"

public export
prodSt: TACSt TACData -> TACSt TACData -> TACSt TACData
prodSt (MkSt x) (MkSt y) = MkSt (prodData x y)

public export
data TACOp: Type -> Type where
  (::=)  : (st: TACSt datTy) -> (src: datTy) -> TACOp datTy
  (<<=)  : (dst: datTy) -> (st: TACSt datTy) -> TACOp datTy
  ADD    : (src1: datTy) -> (src2: datTy) -> (dst: datTy) -> TACOp datTy
  CONCAT : (src1: datTy) -> (src2: datTy) -> (dst: datTy) -> TACOp datTy
  AND    : (src1: datTy) -> (src2: datTy) -> (dst: datTy) -> TACOp datTy
  OR     : (src1: datTy) -> (src2: datTy) -> (dst: datTy) -> TACOp datTy
  XOR    : (src1: datTy) -> (src2: datTy) -> (dst: datTy) -> TACOp datTy
  EQ     : (src1: datTy) -> (src2: datTy) -> (dst: datTy) -> TACOp datTy
  LTU    : (src1: datTy) -> (src2: datTy) -> (dst: datTy) -> TACOp datTy
  LT     : (src1: datTy) -> (src2: datTy) -> (dst: datTy) -> TACOp datTy
  MUX21  : (src1: datTy) -> (src2: datTy) -> (src3: datTy) 
        -> (dst:  datTy) -> TACOp datTy
  SLL    : Nat -> (src: datTy) -> (dst: datTy) -> TACOp datTy
  SRL    : Nat -> (src: datTy) -> (dst: datTy) -> TACOp datTy
  SRA    : Nat -> (src: datTy) -> (dst: datTy) -> TACOp datTy
  NOT    : (src: datTy) -> (dst: datTy) -> TACOp datTy
  SLICE  : Nat -> Nat -> (src: datTy) -> (dst: datTy) -> TACOp datTy
  MULT   : (src1: datTy) -> (src2: datTy) -> (dst: datTy) -> TACOp datTy

export
mapOperands: (a -> a) -> TACOp a -> TACOp a
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
getSrc: TACOp a -> List a
getSrc (x ::= y)         = [y]
getSrc (dst <<= st)      = []
getSrc (ADD x y dst)     = [x, y]
getSrc (CONCAT x y dst)  = [x, y]
getSrc (AND x y dst)     = [x, y]
getSrc (OR x y dst)      = [x, y]
getSrc (XOR x y dst)     = [x, y]
getSrc (EQ x y dst)      = [x, y]
getSrc (LTU x y dst)     = [x, y]
getSrc (LT x y dst)      = [x, y]
getSrc (MUX21 x y z dst) = [x, y, z]
getSrc (SLL k x dst)     = [x]
getSrc (SRL k x dst)     = [x]
getSrc (SRA k x dst)     = [x]
getSrc (NOT x dst)       = [x]
getSrc (SLICE k j x dst) = [x]
getSrc (MULT x y dst)    = [x, y]

public export
getDst: TACOp a -> a
getDst ((MkSt x) ::= y)  = x
getDst (dst <<= st)      = dst
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
getDst (MULT _ _ dst)    = dst

public export
findDef: (Eq a) => 
  a -> List (TACOp a) -> Maybe (TACOp a)
findDef x [] = Nothing
findDef x (y :: xs) = 
  if getDst y == x then Just y 
  else findDef x xs

public export
record TAC where
  constructor MkTAC
  input : TACData
  output: TACData
  state : TACSt TACData
  ops   : List (TACOp TACData)

export
Show a => Show (TACSt a) where
  show (MkSt x) = "!\{show x}"
 
ppOp: Show a => TACOp a -> String
ppOp (x ::= y) = 
  "\{show x} ::= \{show y}"
ppOp (x <<= y) = 
  "\{show x} <<= \{show y}"
ppOp (ADD x y dst) = 
  "\{show dst} = \{show x} + \{show y}"
ppOp (CONCAT x y dst) = 
  "\{show dst} = \{show x} :: \{show y}"
ppOp (AND x y dst) = 
  "\{show dst} = \{show x} & \{show y}"
ppOp (OR x y dst) = 
  "\{show dst} = \{show x} | \{show y}"
ppOp (XOR x y dst) = 
  "\{show dst} = \{show x} ^ \{show y}"
ppOp (EQ x y dst) = 
  "\{show dst} = \{show x} == \{show y}"
ppOp (LTU x y dst) = 
  "\{show dst} = \{show x} <U \{show y}"
ppOp (LT x y dst) = 
  "\{show dst} = \{show x} <S \{show y}"
ppOp (MUX21 x y z dst) = 
  "\{show dst} = if \{show x} then \{show y} else \{show z}"
ppOp (SLL k x dst) = 
  "\{show dst} = \{show x} << \{show k}"
ppOp (SRL k x dst) = 
  "\{show dst} = \{show x} >> \{show k}"
ppOp (SRA k x dst) = 
  "\{show dst} = \{show x} >>A \{show k}"
ppOp (NOT x dst) = 
  "\{show dst} = not \{show x}"
ppOp (SLICE k j x dst) = 
  "\{show dst} = (\{show x})<\{show k}:\{show j}>"
ppOp (MULT src1 src2 dst) = 
  "\{show dst} = \{show src1} * \{show src2}"

export
Show a => Show (TACOp a) where
  show = ppOp

export
substOp: (Subst a) 
  => (old: a) -> (new: a) 
  -> TACOp a -> TACOp a
substOp old new x = 
  mapOperands (subst old new) x

public export
substTAC: (old: TACData) -> (new: TACData) 
  -> TAC -> TAC
substTAC old new tac = 
  let subst = subst old new 
      substOps: List _ -> _ 
        = (map $ substOp old new)
  in {input $= subst, output $= subst, ops $= substOps} tac
  
public export
record FTAC where
  constructor MkFTAC
  input : List FTACData
  output: List FTACData
  state : List (TACSt FTACData)
  ops   : List (TACOp FTACData)

public export
substFTAC: (old: FTACData) -> (new: FTACData) 
  -> FTAC -> FTAC
substFTAC old new tac = 
  let subst = subst old new 
      substOps: List _ -> _ 
        = (map $ substOp old new)
  in {input $= map subst, output $= map subst, ops $= substOps} tac

public export
record FTAC2 where
  constructor MkFTAC2
  input : List FTACData
  output: List FTACData
  state : List (TACSt FTACData)
  opGet : List (TACOp FTACData)
  ops   : List (TACOp FTACData)
  opSet : List (TACOp FTACData)    

public export
substFTAC2: (old: FTACData) -> (new: FTACData) 
  -> FTAC2 -> FTAC2
substFTAC2 old new tac = 
  let subst = subst old new 
      substOps: List _ -> _ 
        = (map $ substOp old new)
  in {input  $= map subst, 
      output $= map subst, 
      opGet  $= substOps,
      ops    $= substOps,
      opSet  $= substOps} tac
      
public export
toFTAC: FTAC2 -> FTAC
toFTAC (MkFTAC2 input output state opGet ops opSet) 
  = MkFTAC input output state (opGet++ops++opSet)

export
Eq a => Eq (TACSt a) where
  (==) (MkSt x) (MkSt y) = x == y
