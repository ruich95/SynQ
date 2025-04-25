module Examples.BalanceTree

import Data.SQData
import Sym.Comb
import Impl.HDL
import Impl.Eval

%hide Data.Linear.Interface.seq

rotateL: {a:_} -> {as:_} -> {comb: _} -> (Comb comb)
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

-- rotateL xin (AllP {ty1 = xTy} x (AllP {ty1=yTy} {ty2=zTy} y z))
--   = let (P sX (P sY sZ)) = asSig 
--         x1 = proj1 xin
--         x2 = proj1 $ proj2 xin
--         x3 = proj2 $ proj2 xin
--     in (((xTy, yTy), zTy) ** (prod (prod x1 x2) x3, AllP (AllP x y) z, P (P sX sY) sZ))
-- rotateL xin (AllU x) = (as ** (xin, AllU x, asSig))
-- rotateL xin (AllP {ty1} {ty2} x y) = ((ty1, ty2) ** (xin, AllP x y, asSig))

rotateR: {a:_} -> {as:_} -> {comb: _} -> (Comb comb)
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

-- rotateR_lemma: {as: _} -> {a:_} -> {comb: _} -> (Comb comb)
--   => {auto aSig: Sig a} -> (xin: comb () (a, as)) -> (prf: All (OfType a) as)
--   -> (rotateR {a=a} {as=(a, as)} xin (AllP (AllU Refl) prf)) = ((a, as) ** (xin, (AllP (AllU Refl) prf), P aSig (allSig aSig prf)))
-- rotateR_lemma xin prf = Refl

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

balance: {ty:_} -> {comb: _} -> (Comb comb)
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

balancedReduce: {a:_} -> {default 20 max_iter: Nat} 
  -> {comb:_} -> (Comb comb)
  => {auto aIsSig: Sig a}
  -> {auto allA: All (OfType a) as}
  -> (f: comb (a, a) a)
  -> comb as a
balancedReduce f = 
  lam $ \xin => case balance {max_iter=max_iter} xin {shape=allA} of
                     (ty ** (xin', all', sig')) => app (reduce f) xin'
                     
leftAssoc: {comb:_} -> (Comb comb)
  => {auto aIsSig: Sig a}
  -> (f: comb (a, a) a)
  -> comb ((a, a), a) a
leftAssoc f = lam $ \x => app f (prod (app f $ proj1 x) (proj2 x))

rightAssoc: {comb:_} -> (Comb comb)
  => {auto aIsSig: Sig a}
  -> (f: comb (a, a) a)
  -> comb (a, (a, a)) a
rightAssoc f = lam $ \x => app f (prod (proj1 x) (app f $ proj2 x))

assoc: {a:_} -> {auto aIsSig: Sig a} 
  -> (f: Eval.Combinational (a, a) a) 
  -> Type
assoc f = (x: a) -> (y: a) -> (z: a) 
  -> (runComb (leftAssoc f) $ ((x, y), z)) 
   = (runComb (rightAssoc f) $ (x, (y, z)))

reduceEq: {a:_} -> {as:_} -> {auto aIsSig: Sig a} -> (allA: All (OfType a) as)
  -> (f: Eval.Combinational (a, a) a) -> (xin: as)
  -> (assoc_f: assoc f)
  -> (runComb (reduce {as=as} {prf1=aIsSig} f) $ xin) = (runComb (balancedReduce {max_iter=1} f) $ xin)
reduceEq (AllU x) f xin assoc_f = Refl
reduceEq {a} (AllP {ty1=ty1} {ty2=ty2} all1 all2) f xin assoc_f with (allBalanced (AllP all1 all2))
  reduceEq {a} (AllP {ty1=ty1} {ty2=ty2} all1 all2) f (xin1, xin2) assoc_f | False  with (getShape (AllP all1 all2))
    reduceEq (AllP {ty1=ty1} {ty2=ty2} all1 all2) f (xin1, xin2) assoc_f | False  | Balance = ?case_balance
    reduceEq {a} (AllP {ty1=a} {ty2=ty2} (AllU Refl) all2) f (xin1, xin2) assoc_f | False  | LL = Refl
    reduceEq (AllP {ty1=(ty11, ty12)} {ty2=ty2} (AllP x y) all2) f (xin1, xin2) assoc_f | False  | LL with %syntactic (xin1)
      reduceEq (AllP {ty1=(ty11, ty12)} {ty2=ty2} (AllP x y) all2) f (xin1, xin2) assoc_f | False  | LL | (xin11, xin12) 
        = let assoc_prf = assoc_f (runComb (reduce f) $ xin11) 
                                  (runComb (reduce f) $ xin12) 
                                  (runComb (reduce f) $ xin2)
          in rewrite assoc_prf in Refl
    reduceEq (AllP {ty1=ty1} {ty2=ty2} all1 all2) f (xin1, xin2) assoc_f | False  | RR = ?case_rr
    reduceEq {a} (AllP {ty1=a} {ty2=ty2} (AllU Refl) all2) f (xin1, xin2) assoc_f | False  | (LR _ _ _) = Refl
    reduceEq {a} (AllP {ty1=(ty11, ty12)} {ty2=ty2} (AllP x y) all2) f (xin1, xin2) assoc_f | False  | (LR _ _ _) with %syntactic (xin1)
      reduceEq {a} (AllP {ty1=(ty11, ty12)} {ty2=a} (AllP x y) (AllU Refl)) f (xin1, xin2) assoc_f 
          | False  | (LR _ _ _) | (xin11, xin12) with %syntactic (y)
        reduceEq {a} (AllP {ty1=(ty11, a)} {ty2=a} (AllP x y) (AllU Refl)) f (xin1, xin2) assoc_f 
          | False  | (LR _ _ _) | (xin11, xin12) | (AllU Refl) = assoc_f (runComb (reduce f) $ xin11) xin12 xin2
        reduceEq {a} (AllP {ty1=(ty11, (ty121, ty122))} {ty2=a} (AllP x y) (AllU Refl)) f (xin1, xin2) assoc_f 
          | False  | (LR _ _ _) | (xin11, xin12) | (AllP z w) = 
            let assoc_prf1 = assoc_f (runComb (reduce f) $ xin11) 
                                     ((runComb f) ((runComb (reduce f) $ fst xin12), 
                                                   (runComb (reduce f) $ snd xin12))) 
                                     xin2
                assoc_prf2 = assoc_f (runComb (reduce f) $ fst xin12) 
                                     (runComb (reduce f) $ snd xin12)
                                     xin2
                assoc_prf3 = sym $ assoc_f (runComb (reduce f) $ xin11) 
                                           (runComb (reduce f) $ fst xin12) 
                                           (runComb f $ ((runComb (reduce f) $ snd xin12), xin2))
            in rewrite assoc_prf1 in 
               rewrite assoc_prf2 in 
               assoc_prf3
      reduceEq (AllP {ty1=(ty11, ty12)} {ty2=(ty1, ty2)} (AllP x1 y1) (AllP x2 y2)) f (xin1, xin2) assoc_f 
          | False  | (LR _ _ _) | (xin11, xin12) with %syntactic (y1)
        reduceEq (AllP {ty1=(ty11, a)} {ty2=(ty1, ty2)} (AllP x1 y1) (AllP x2 y2)) f (xin1, xin2) assoc_f 
          | False  | (LR _ _ _) | (xin11, xin12) | (AllU Refl) = 
            assoc_f (runComb (reduce f) $ xin11) xin12 
                    (runComb f $ (runComb (reduce f) $ fst xin2, 
                                  runComb (reduce f) $ snd xin2))
        reduceEq (AllP {ty1=(ty11, ty121, ty122)} {ty2=(ty1, ty2)} (AllP x1 y1) (AllP x2 y2)) f (xin1, xin2) assoc_f 
          | False  | (LR _ _ _) | (xin11, xin12) | (AllP z w) = 
            let assoc_prf1 = sym $ assoc_f (runComb (reduce f) $ xin11) 
                                           (runComb (reduce f) $ fst xin12) 
                                           (runComb (reduce f) $ snd xin12)
                assoc_prf2 = assoc_f (runComb f $ (runComb (reduce f) $ xin11, 
                                                   runComb (reduce f) $ fst xin12))
                                     (runComb (reduce f) $ snd xin12)
                                     (runComb f $ (runComb (reduce f) $ fst xin2, 
                                                   runComb (reduce f) $ snd xin2))
            in rewrite assoc_prf1 in assoc_prf2
    reduceEq (AllP {ty1=ty1} {ty2=ty2} all1 all2) f (xin1, xin2) assoc_f | False  | (RL left rightL rightR) = ?case_rl
  reduceEq (AllP all1 all2) f xin assoc_f | True = Refl

%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

tAll: All (OfType $ BitVec 8) (BitVec 8, ((BitVec 8, (BitVec 8, (BitVec 8, BitVec 8))) , BitVec 8))
tAll = AllP (AllU Refl) 
            (AllP (AllP (AllU Refl) 
                        (AllP (AllU Refl) (AllP (AllU Refl) 
                                                (AllU Refl)))) 
                  (AllU Refl))

adder: {comb:_} -> {n:_} 
  -> (Comb comb, Primitive comb)
  => comb (BitVec n, BitVec n) (BitVec n)
adder = lam $ \x => lower' n (add (proj1 x) (proj2 x))

balancedSum: {comb: _} -> (Comb comb, Primitive comb)
  => comb (BitVec 8, ((BitVec 8, (BitVec 8, (BitVec 8, BitVec 8))) , BitVec 8)) 
          (BitVec 8)
balancedSum = balancedReduce adder {allA=tAll}
