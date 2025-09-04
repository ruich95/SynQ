module Impl.TAC.PPrint

import Impl.TAC.Types
import Data.BitVec 
import Data.LC

ppTy: TACTy -> String
ppTy (BvTy width) = 
  "BV \{show width}"
ppTy (ProdTy a b) = 
  "(\{ppTy a}, \{ppTy b})"
ppTy UnitTy = "()"

ppName: Name -> String
ppName Anon = "_"
ppName (NM str) = str

ppData: TACData -> String
ppData (Const {n} x) = 
  "\{show x}: BV \{show n}"
ppData U = "() : ()"
ppData (Var nm ty1) = 
  "\{ppName nm}: \{ppTy ty1}"

ppSt: TACSt -> String
ppSt (MkSt name ty) = 
  "\{ppName name}: \{ppTy ty}"
  
ppGl: TACGl1 -> String
ppGl (PROD x y dst) = 
  "\{ppData dst} = (\{ppData x}, \{ppData y})"
ppGl (PROJ1 x dst) = 
  "\{ppData dst} = proj1 \{ppData x}"
ppGl (PROJ2 x dst) = 
  "\{ppData dst} = proj2 \{ppData x}"

ppOp: TACOp1 -> String
ppOp (x ::= y) = 
  "\{ppData x} ::= \{ppData y}"
ppOp (x <<= y) = 
  "\{ppData x} <<= \{ppData y}"
ppOp (ADD x y dst) = 
  "\{ppData dst} = \{ppData x} + \{ppData y}"
ppOp (CONCAT x y dst) = 
  "\{ppData dst} = \{ppData x} :: \{ppData y}"
ppOp (AND x y dst) = 
  "\{ppData dst} = \{ppData x} & \{ppData y}"
ppOp (OR x y dst) = 
  "\{ppData dst} = \{ppData x} | \{ppData y}"
ppOp (XOR x y dst) = 
  "\{ppData dst} = \{ppData x} ^ \{ppData y}"
ppOp (EQ x y dst) = 
  "\{ppData dst} = \{ppData x} == \{ppData y}"
ppOp (LTU x y dst) = 
  "\{ppData dst} = \{ppData x} <U \{ppData y}"
ppOp (LT x y dst) = 
  "\{ppData dst} = \{ppData x} <S \{ppData y}"
ppOp (MUX21 x y z dst) = 
  "\{ppData dst} = if \{ppData x} then \{ppData y} else \{ppData z}"
ppOp (SLL k x dst) = 
  "\{ppData dst} = \{ppData x} << \{show k}"
ppOp (SRL k x dst) = 
  "\{ppData dst} = \{ppData x} >> \{show k}"
ppOp (SRA k x dst) = 
  "\{ppData dst} = \{ppData x} >>A \{show k}"
ppOp (NOT x dst) = 
  "\{ppData dst} = not \{ppData x}"
ppOp (SLICE k j x dst) = 
  "\{ppData dst} = (\{ppData x})[\{show k}:\{show j}]"
  
ppAtom: TACAtom1 -> String
ppAtom (Gl x) = ppGl x
ppAtom (Op x) = ppOp x

export
ppTAC: (1 _: LC TACSt TAC1) -> List String
ppTAC ((MkSt name ty) # (MkTAC1 input output ops)) = 
  "input: \{ppData input}" 
  :: "output: \{ppData output}" 
  :: "state: \{ppSt (MkSt name ty)}" 
  :: map ppAtom ops
