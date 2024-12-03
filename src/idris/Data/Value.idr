module Data.Value

import Data.BitVec

public export
data Value: (len: Nat) -> Type where
  UV: Value len
  V: BitVec len -> Value len
%name Value val, val1, val2

export
{len:_} -> Eq (Value len) where
  (==) UV UV = True
  (==) (V b1) (V b2) = (b1 == b2)
  (==) _ _ = False

export
{len:_} -> Show (Value len) where
  show UV = "unknown value of len" ++ show len
  show (V x) = show x
