module Impl.Eval.CombPrimitive

import Sym.Comb.CombPrimitive
import Impl.Eval.Eval

import Data.BitVec
import Data.Nat

public export
Primitive Combinational where
  const x = MkComb (\() => x)
  
  add (MkComb x) (MkComb y) = MkComb $ \u => bvAdd (x u) (y u)
  
  concat (MkComb x) (MkComb y) = MkComb $ \u => bvConcat (x u) (y u)
  
  and (MkComb x) (MkComb y) = MkComb $ \u => bvAnd (x u) (y u)
  
  or (MkComb x) (MkComb y) = MkComb $ \u => bvOr (x u) (y u)
  
  not (MkComb x) = MkComb $ \u => bvNot (x u)
  
  xor (MkComb x) (MkComb y) = MkComb $ \u => bvXor (x u) (y u)
  
  shiftLL sht (MkComb x) = MkComb $ \u => bvSll sht (x u)
  
  shiftRL sht (MkComb x) = MkComb $ \u => bvSrl sht (x u)
  
  shiftRA sht (MkComb x) = MkComb $ \u => bvSra sht (x u)
  
  slice lower upper (MkComb x) = MkComb $ \u => bvSlice lower upper (x u)
  
  mux21 (MkComb b) x y = if (b ()) == 1 then x else y
                         
  lt (MkComb x) (MkComb y) = MkComb $ \u => bvLt (x u) (y u)
    
  ltu (MkComb x) (MkComb y) = MkComb $ \u => bvLtu (x u) (y u)
  
  eq (MkComb x) (MkComb y) = MkComb  $ \u => if (x u) == (y u) then 1 else 0
  
  
