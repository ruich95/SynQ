module Examples.BalanceTree

import Data.SQData
import Sym.Comb
import Impl.HDL
import Impl.Eval

%hide Data.Linear.Interface.seq

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

balance: {comb: _} -> (Comb comb)
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
                       (ty' ** (tr', all', sig')) = rotateR (prod left right') (AllP shapeL allR)
                   in balance {max_iter=k} tr' {shape=all'}
  
tAll: All (OfType $ BitVec 8) (BitVec 8, ((BitVec 8, (BitVec 8, (BitVec 8, BitVec 8))) , BitVec 8))
tAll = AllP (AllU Refl) 
            (AllP (AllP (AllU Refl) 
                        (AllP (AllU Refl) (AllP (AllU Refl) 
                                                (AllU Refl)))) 
                  (AllU Refl))

balancedReduce: {default 20 max_iter: Nat} 
  -> {comb:_} -> (Comb comb)
  => {auto aIsSig: Sig a}
  -> {auto allA: All (OfType a) as}
  -> (f: comb (a, a) a)
  -> comb as a
balancedReduce f = 
  lam $ \xin => case balance {max_iter=max_iter} xin {shape=allA} of
                     (ty ** (xin', all', sig')) => app (reduce f) xin'

balance_lemma1: {ty:_} -> {as:_} -> {bs:_} -> {comb: _} -> (Comb comb) => {auto asSig: Sig as} -> {auto bsSig: Sig bs} 
  -> (xin: comb () (as, bs)) -> (shape1: All (OfType ty) as) -> (shape2: All (OfType ty) bs)
  -> (allBalanced {ty=ty} (the (All (OfType ty) (as, bs)) $ AllP {ty1=as} {ty2=bs} shape1 shape2) = True) 
  -> (balance {comb=comb} {max_iter=1} {ty=ty} {asSig=(P asSig bsSig)} xin {shape=(AllP {ty1=as} {ty2=bs} shape1 shape2)})
   = ((as, bs) ** (xin, (the (All (OfType ty) (as, bs)) $ AllP {ty1=as} {ty2=bs} shape1 shape2), (P asSig bsSig)))
balance_lemma1 xin shape1 shape2 prf = rewrite prf in Refl

combLemma: (xin: Eval.Combinational () as) -> MkComb (\value => xin .runComb ()) = xin

reduceEq: {a:_} -> {as:_} -> {auto aIsSig: Sig a} -> (allA: All (OfType a) as)
  -> (f: Eval.Combinational (a, a) a) -> (xin: Eval.Combinational () as)
  -> (runComb $ app (reduce {prf1=aIsSig} f) xin) () = (runComb $ app (balancedReduce {max_iter=1} {aIsSig=aIsSig} {allA = allA} f) xin) ()
reduceEq (AllU x) f xin = Refl
reduceEq (AllP {ty1=ty1} {ty2=ty2} all1 all2) f xin with (proj1 xin, proj2 xin)
  reduceEq (AllP {ty1=ty1} {ty2=ty2} all1 all2) f xin | (xin1, xin2) with (allBalanced (AllP all1 all2)) proof p
    reduceEq (AllP {ty1=ty1} {ty2=ty2} all1 all2) f xin | (xin1, xin2) | False = ?rhs_rhs_0
    reduceEq (AllP {ty1=ty1} {ty2=ty2} all1 all2) f xin | (xin1, xin2) | True 
      = let eq_prf = balance_lemma1 {ty=a} {as=ty1} {bs=ty2} {comb=Eval.Combinational} xin all1 all2 p 
        in rewrite combLemma xin in rewrite eq_prf in ?rhs

%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

adder: {comb:_} -> {n:_} 
  -> (Comb comb, Primitive comb)
  => comb (BitVec n, BitVec n) (BitVec n)
adder = lam $ \x => lower' n (add (proj1 x) (proj2 x))

balancedSum: {comb: _} -> (Comb comb, Primitive comb)
  => comb (BitVec 8, ((BitVec 8, (BitVec 8, (BitVec 8, BitVec 8))) , BitVec 8)) 
          (BitVec 8)
balancedSum = balancedReduce adder {allA=tAll}
