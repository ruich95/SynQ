import SynQ

%hide Data.Linear.Interface.seq

interface PrimitiveInt (comb: Type -> Type -> Type) where
  add: comb () Int -> comb () Int -> comb () Int
  fromBV: comb () (BitVec 32) -> comb () Int
  toBV: comb () Int -> comb () (BitVec 32)
  
{comb:_} -> Primitive comb => PrimitiveInt comb where
  add x y = fromBV $ slice 0 32 (CombPrimitive.add (toBV x) (toBV y))
  fromBV x = ?rhs
  toBV x = ?rhs_2
  
adder: {comb: _} -> (Comb comb, PrimitiveInt comb)
  => comb (Int, Int) Int
adder = lam $ \x => add (proj1 x) (proj2 x)
