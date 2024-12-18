module Impl.Eval.CombPrimitive

import Sym.Comb.CombPrimitive
import Impl.Eval.Eval

import Data.BitVec
import Data.Nat
import Data.Bits

public export
Primitive Combinational where
  const x = MkComb (\() => x)
  
  add (MkComb x) (MkComb y) = MkComb $ \() => bvAdd (x ()) (y ())
  
  concat (MkComb x) (MkComb y) = MkComb $ \() => bvConcat (x ()) (y ())
  
  and (MkComb x) (MkComb y) = MkComb $ \() => bvAnd (x ()) (y ())
  
  or (MkComb x) (MkComb y) = MkComb $ \() => bvOr (x ()) (y ())
  
  not (MkComb x) = MkComb $ \() => bvNot (x ())
  
  xor (MkComb x) (MkComb y) = MkComb $ \() => bvXor (x ()) (y ())
  
  shiftLL sht (MkComb x) = MkComb $ \() => bvSll sht (x ())
  
  shiftRL sht (MkComb x) = MkComb $ \() => bvSrl sht (x ())
  
  shiftRA sht (MkComb x) = MkComb $ \() => bvSra sht (x ())
  
  slice lower upper (MkComb x) = MkComb $ \() => bvSlice lower upper (x ())
  
  mux21 (MkComb b) x y = if (b ()) == (BV 1) then x else y
                         
  lt (MkComb x) (MkComb y) = MkComb $ \() => bvLt (x ()) (y ())
    
  ltu (MkComb x) (MkComb y) = MkComb $ \() => bvLtu (x ()) (y ())
  
  eq (MkComb x) (MkComb y) = MkComb  $ \() => if (x ()) == (y ()) then (BV 1) else (BV 0)
  
  
