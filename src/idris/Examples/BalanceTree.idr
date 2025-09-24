module Examples.BalanceTree

import Data.SQData
import Sym.Comb
import Sym.Seq
import Impl.HDL
import Impl.Eval

%hide Data.Linear.Interface.seq

rotateL: {a:_} -> {as:_} -> (Comb comb)
  => {auto asSig: Sig as} -> comb () as -> (prf: All (OfType a) as)
  -> (bs: Type ** (comb () bs, All (OfType a) bs, Sig bs))
rotateL {as = a} xin (AllU Refl) = (a ** (xin, (AllU Refl, asSig)))
rotateL {a} {as = (ty1, ty2)} xin (AllP x y) with (y)
  rotateL {a} {as = (ty1, a)} xin (AllP x y) | (AllU Refl) = ((ty1, a) ** (xin, (AllP x y, asSig)))
  rotateL {as = (ty1, (ty21, ty22))} xin (AllP x y) | (AllP z w) -- = ?rotateL_rhs_1_rhs_1
    = let (P sX (P sZ sW)) = asSig 
          x1 = proj1 xin
          x2 = proj1 $ proj2 xin
          x3 = proj2 $ proj2 xin
      in (((ty1, ty21), ty22) ** (prod (prod x1 x2) x3, AllP (AllP x z) w, P (P sX sZ) sW))

rotateR: {a:_} -> {as:_} -> (Comb comb)
  => {auto asSig: Sig as} -> comb () as -> (prf: All (OfType a) as)
  -> (bs: Type ** (comb () bs, All (OfType a) bs, Sig bs))
rotateR {as = a} xin (AllU Refl) = (a ** (xin, (AllU Refl, asSig)))
rotateR {a} {as=(ty1, ty2)} xin (AllP y z) with (y)
  rotateR {a} {as=(a, ty2)} xin (AllP y z) | (AllU Refl) = ((a, ty2) ** (xin, (AllP y z, asSig)))
  rotateR {as=((ty11, ty12), ty2)} xin (AllP y z) | (AllP x w)
    = let (P (P sX sW) sZ) = asSig 
          x1 = proj1 $ proj1 xin
          x2 = proj2 $ proj1 xin
          x3 = proj2 xin
      in ((ty11, (ty12, ty2)) ** (prod x1 (prod x2 x3), AllP x (AllP w z), P sX (P sW sZ)))

depth: (prf: All (OfType ty) as) -> Nat
depth (AllU x) = 0
depth (AllP x y) = S (max (depth x) (depth y))

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
  getShape (AllP (AllP ll lr) y) | (AllP rl rr) 
    = let dl = depth (AllP ll lr) 
          dr = depth (AllP rl rr) 
      in if dl == dr || dl == S dr || dr == S dl 
         then Balance 
         else if dl > dr 
              then if depth ll > depth lr 
                   then LL 
                   else LR ll lr (AllP rl rr) 
              else if depth rr > depth rl 
                   then RR 
                   else RL (AllP ll lr) rl rr
                   
allBalanced: All (OfType ty) as -> Bool
allBalanced (AllU x) = True
allBalanced (AllP l r) 
  = let dl = depth l
        dr = depth r 
    in allBalanced l && allBalanced r 
    && ((dl == dr) || (dl == S dr) || (S dl == dr))

balance: {ty:_} -> (Comb comb)
  => {default 20 max_iter: Nat} 
  -> {auto asSig: Sig as} -> comb () as -> {auto shape: All (OfType ty) as}
  -> (bs: Type ** (comb () bs, All (OfType ty) bs, Sig bs))
balance x {shape = (AllU y)} = (as ** (x, (AllU y, asSig)))
balance {max_iter = 0} x {shape = (AllP {ty1 = ty1} {ty2 = ty2} y z)} 
  = ((ty1, ty2) ** (x, (AllP y z, asSig)))
balance {max_iter = (S k)} {asSig=P lSig rSig} tr 
        {shape = (AllP {ty1 = ty1} {ty2 = ty2} shapeL shapeR)} 
  = if allBalanced (AllP shapeL shapeR) then ((ty1, ty2) ** (tr, (AllP shapeL shapeR, P lSig rSig)))
    else let left  = proj1 tr
             right = proj2 tr
         in case getShape (AllP shapeL shapeR) of
              Balance => 
                let (lty ** (left', allL, sigL))  = balance {max_iter = S k} left  {shape=shapeL}
                    (rty ** (right', allR, sigR)) = balance {max_iter = S k} right {shape=shapeR}
                in ((lty, rty) ** (prod left' right', AllP allL allR, P sigL sigR))
              LL => 
                let (ty' ** (tr', all', sig')) = rotateR tr (AllP shapeL shapeR)
                in balance {max_iter=k} tr' {shape=all'}
              RR => 
                let (ty' ** (tr', all', sig')) = rotateL tr (AllP shapeL shapeR)
                in balance {max_iter=k} tr' {shape=all'}
              (LR leftL leftR x) =>
                let (tyl ** (left', allL, sigL)) = rotateL left shapeL
                    (ty' ** (tr', all', sig')) = rotateR (prod left' right) (AllP allL shapeR)
                in balance {max_iter=k} tr' {shape=all'}
              (RL x rightL rightR) => 
                let (tyr ** (right', allR, sigR)) = rotateR right shapeR
                    (ty' ** (tr', all', sig')) = rotateL (prod left right') (AllP shapeL allR)
                in balance {max_iter=k} tr' {shape=all'}

export
balancedReduce: {a:_} -> {default 20 max_iter: Nat} 
  -> (Comb comb)
  => {auto aIsSig: Sig a}
  -> {auto allA: All (OfType a) as}
  -> (f: comb (a, a) a)
  -> comb as a
balancedReduce f = 
  lam $ \xin => case balance {max_iter=max_iter} xin {shape=allA} of
                     (ty ** (xin', all', sig')) => app (reduce f) xin'
