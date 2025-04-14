module Examples.BalanceTree

import Data.SQData
import Sym.Comb

rotateL: {comb: _} -> (Comb comb)
  => {auto asSig: Sig as} -> comb () as -> (prf: All (OfType ty) as)
  -> (bs: Type ** (comb () bs, All (OfType ty) bs, Sig bs))
rotateL xin (AllP {ty1 = xTy} x (AllP {ty1=yTy} {ty2=zTy} y z))
  = let (P sX (P sY sZ)) = asSig 
        x1 = proj1 xin
        x2 = proj1 $ proj2 xin
        x3 = proj2 $ proj2 xin
    in (((xTy, yTy), zTy) ** (prod (prod x1 x2) x3, AllP (AllP x y) z, P (P sX sY) sZ))
rotateL xin (AllU x) = (as ** (xin, AllU x, asSig))
rotateL xin (AllP {ty1} {ty2} x y) = ((ty1, ty2) ** (xin, AllP x y, asSig))

rotateR: {comb: _} -> (Comb comb)
  => {auto asSig: Sig as} -> comb () as -> (prf: All (OfType ty) as)
  -> (bs: Type ** (comb () bs, All (OfType ty) bs, Sig bs))
rotateR xin (AllP {ty2=zTy} (AllP {ty1=xTy} {ty2=yTy} x y) z) 
  = let (P (P sX sY) sZ) = asSig 
        x1 = proj1 $ proj1 xin
        x2 = proj2 $ proj1 xin
        x3 = proj2 xin
    in ((xTy, (yTy, zTy)) ** (prod x1 (prod x2 x3), AllP x (AllP y z), P sX (P sY sZ)))
rotateR xin (AllU x) = (as ** (xin, (AllU x, asSig)))
rotateR xin (AllP {ty1} {ty2} x y) = ((ty1, ty2) ** (xin, (AllP x y, asSig)))

depth: (prf: All (OfType ty) as) -> Nat
depth (AllU x) = 0
depth (AllP x y) = max (depth x) (depth y)

data Shape: Type where
  Balance: Shape
  LL: Shape
  RR: Shape
  LR: (leftL: All (OfType ty) as) -> (leftR: All (OfType ty) bs) 
   -> (right: All (OfType ty) cs) -> Shape
  RL: (left: All (OfType ty) as) -> (rightL: All (OfType ty) bs) 
   -> (rightR: All (OfType ty) cs) -> Shape
   
getShape: All (OfType ty) as -> Shape
getShape (AllU x) = Balance
getShape (AllP (AllU x) (AllU y)) = Balance
getShape (AllP (AllU x) (AllP rl rr)) 
  = if depth rl > depth rr then RL (AllU x) rl rr else RR
getShape (AllP (AllP x z) y) with (y)
  getShape (AllP (AllP ll lr) y) | (AllU x) 
    = if depth lr > depth ll then LR ll lr (AllU x) else LL
  getShape (AllP (AllP ll lr) y) | (AllP rl rr) = ?rhs_3_rhs_1

-- getShape (AllP (AllU x) (AllU y)) = Balance
-- getShape (AllP (AllU x) (AllP rl rr)) = ?rhs -- if depth rl > depth rr then RL (AllU x) rl rr else RR
-- getShape (AllP (AllP ll lr) (AllU z)) = ?rhsw -- if depth lr > depth ll then LR ll lr (AllU z) else LL
-- getShape (AllP (AllP x y) (AllP z w)) = ?rhs_4

rotateL2: {comb: _} -> (Comb comb)
  => {auto asSig: Sig as} -> comb () as -> {auto prf: All (OfType ty) as}
  -> (bs: Type ** (comb () bs, All (OfType ty) bs, Sig bs))
rotateL2 x = 
  let (ty1 ** (y, yPrf, ySig1)) = rotateL x prf
  in rotateL y yPrf
  
test: {comb: _} -> (Comb comb, Primitive comb)
  => comb () (BitVec 8, (BitVec 8, (BitVec 8, BitVec 8)))
  
t_prf: All (OfType $ BitVec 8) (BitVec 8, (BitVec 8, (BitVec 8, BitVec 8)))
t_prf = AllP (AllU Refl) (AllP (AllU Refl) (AllP (AllU Refl) (AllU Refl)))

test2: {comb: _} -> (Comb comb, Primitive comb)
  => (ty:Type ** comb () ty)
test2 = let (ty ** (x, _, _)) = rotateL {comb} test t_prf in (ty ** x)

test2': {comb: _} -> (Comb comb, Primitive comb)
  => fst (BalanceTree.test2 {comb=comb}) = ((BitVec 8, BitVec 8), (BitVec 8, BitVec 8))
test2' = Refl
