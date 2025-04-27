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

balance_lemma_ty: (max_iter: Nat) -> Type 
balance_lemma_ty max_iter =
     {a:_} -> {as:_} -> {auto aIsSig: Sig a} -> (allA: All (OfType a) as)
  -> (f: Eval.Combinational (a, a) a) -> (xin: as)
  -> (assoc_f: assoc f)
  -> {as': _} -> {xin': _} -> {allA': All (OfType a) as'} -> {sigAs': Sig as'}
  -> (as' ** (xin', allA', sigAs')) 
  = balance {ty=a} {comb=Eval.Combinational} 
            {max_iter=max_iter} {asSig=allSig aIsSig allA} 
            (MkComb $ \x => xin) {shape=allA}
  -> (runComb (reduce {as=as} {prf2=allA} f) $ xin) 
  = ((runComb $ app (reduce {prf2=allA'} f) xin') ())

extFst : {p: a -> Type} -> {t1 : (x: a ** p x)} -> {t2 : (y: a ** p y)}
  -> t1 = t2 -> t1.fst = t2.fst
extFst Refl = Refl

extSnd : {p: a -> Type} -> {t1 : (x: a ** p x)} -> {t2 : (y: a ** p y)}
  -> (prf : t1 = t2) -> (snd t1) = (rewrite extFst prf in snd t2)
extSnd Refl = Refl

balance_lemma_base: {a:_} -> {as:_} -> {auto aIsSig: Sig a} -> (allA: All (OfType a) as)
  -> (f: Eval.Combinational (a, a) a) -> (xin: as)
  -> (assoc_f: assoc f)
  -> {as': _} -> {xin': _} -> {allA': All (OfType a) as'} -> {sigAs': Sig as'}
  -> (as' ** (xin', allA', sigAs')) 
  = balance {ty=a} {comb=Eval.Combinational} {max_iter=0} {asSig=allSig aIsSig allA} 
            (MkComb $ \x => xin) {shape=allA}
  -> (runComb (reduce {as=as} {prf2=allA} f) $ xin) = ((runComb $ app (reduce {prf2=allA'} f) xin') ())
balance_lemma_base {as = as} (AllU x) f xin assoc_f Refl = Refl
balance_lemma_base {as = (ty1, ty2)} (AllP x y) f xin assoc_f prf_unpack 
  =   let prf_xin'  = cong fst $ extSnd prf_unpack
          prf_allA' = cong (fst . snd) $ extSnd prf_unpack
      in rewrite prf_allA' in 
         rewrite prf_xin'  in Refl

balance_lemma_succ : (k: Nat) -> (prev: balance_lemma_ty k) 
  -> balance_lemma_ty (S k)
balance_lemma_succ {as = as} k prev (AllU x) f xin assoc_f Refl = Refl
balance_lemma_succ {aIsSig} k prev {a} {as=(ty1, ty2)} (AllP {ty1=ty1} {ty2=ty2} x y) f xin assoc_f unpack_prf with (allBalanced (AllP {ty1=ty1} {ty2=ty2} x y))
  balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=(ty1, ty2)} (AllP {ty1=ty1} {ty2=ty2} x y) f xin1 assoc_f unpack_prf | False with (getShape (AllP {ty1=ty1} {ty2=ty2} x y))
    balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=(ty1, ty2)} (AllP {ty1=ty1} {ty2=ty2} x y) f xin assoc_f unpack_prf | False | Balance with (balance {comb=Eval.Combinational} {asSig= allSig aIsSig x} {max_iter= S k} (MkComb $ \x => fst xin) {shape=x}) proof prf_left
      balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=(ty1, ty2)} (AllP {ty1=ty1} {ty2=ty2} x y) f xin assoc_f unpack_prf | False | Balance | (lty ** (left', (allL, sigL))) with (balance {comb=Eval.Combinational} {asSig= allSig aIsSig y} {max_iter= S k} (MkComb $ \x => snd xin) {shape=y}) proof prf_right
        balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=(ty1, ty2)} (AllP {ty1=ty1} {ty2=ty2} x y) f xin assoc_f unpack_prf | False | Balance | (lty ** (left', (allL, sigL))) | (rty ** (right', (allR, sigR))) = 
          let prf_eq_l = balance_lemma_succ k prev x f (fst xin) assoc_f (sym prf_left)
              prf_eq_r = balance_lemma_succ k prev y f (snd xin) assoc_f (sym prf_right)
              prf_xin' = cong fst $ extSnd unpack_prf
              prf_shape = cong (fst . snd) $ extSnd unpack_prf
          in rewrite prf_xin' in 
             rewrite prf_shape in 
             rewrite prf_eq_l in 
             rewrite prf_eq_r in Refl
    balance_lemma_succ {aIsSig = aIsSig} k prev {a = ty1} {as=(ty1, ty2)} (AllP {ty1=ty1} {ty2=ty2} (AllU Refl) y) f (xin1, xin2) assoc_f unpack_prf | False | LL = 
      prev (AllP {ty1=ty1} {ty2=ty2} (AllU Refl) y) f (xin1, xin2) assoc_f unpack_prf
    balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=((ty11, ty12), ty2)} (AllP {ty1=(ty11, ty12)} {ty2=ty2} (AllP x y) z) f ((xin11, xin12), xin2) assoc_f unpack_prf | False | LL = 
      let prf = sym $ prev (AllP {ty1=ty11} {ty2=(ty12, ty2)} x (AllP y z)) f (xin11, (xin12, xin2)) assoc_f unpack_prf
          prf_assoc = assoc_f (runComb (reduce f) $ xin11) 
                              (runComb (reduce f) $ xin12) 
                              (runComb (reduce f) $ xin2)
      in rewrite prf in prf_assoc
    balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=(ty1, ty2)} (AllP {ty1=ty1} {ty2=ty2} x y) f xin assoc_f unpack_prf | False | RR = ?sym_ll
    balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=(ty1, ty2)} (AllP {ty1=ty1} {ty2=ty2} x y) f (xin1, xin2) assoc_f unpack_prf | False | (LR _ _ _) with (x)
      balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=(a, ty2)} (AllP {ty1=a} {ty2=ty2} x y) f (xin1, xin2) assoc_f unpack_prf | False | (LR _ _ _) | (AllU Refl) = 
        prev (AllP {ty1=a} {ty2=ty2} (AllU Refl) y) f (xin1, xin2) assoc_f unpack_prf
      balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=((ty11, ty12), ty2)} (AllP {ty1=(ty11, ty12)} {ty2=ty2} _ z) f (xin1, xin2) assoc_f unpack_prf | False | (LR _ _ _) | (AllP x y) with (y)
        balance_lemma_succ {aIsSig = aIsSig} k prev {a = ty12} {as=((ty11, ty12), ty2)} (AllP {ty1=(ty11, ty12)} {ty2=ty2} _ z) f ((xin11, xin12), xin2) assoc_f unpack_prf | False | (LR _ _ _) | (AllP x _) | (AllU Refl) = 
          let prf_prev = sym $ prev (AllP {ty1=ty11} {ty2=(ty12, ty2)} x (AllP (AllU Refl) z)) f (xin11, xin12, xin2) assoc_f unpack_prf
              prf_assoc = assoc_f (runComb (reduce f) $ xin11) 
                                  (xin12) 
                                  (runComb (reduce f) $ xin2)
          in rewrite prf_prev in prf_assoc
        balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=((ty11, (ty1, ty2)), ty2)} (AllP {ty1=(ty11, (ty121, ty122))} {ty2=ty2} _ z) f ((xin11, (xin121, xin122)), xin2) assoc_f unpack_prf | False | (LR _ _ _) | (AllP x _) | (AllP y w) = 
          let prf_prev = sym $ prev (AllP {ty1=(ty11, ty121)} {ty2=(ty122, ty2)} (AllP x y) (AllP w z)) f ((xin11, xin121), (xin122, xin2)) assoc_f unpack_prf
              prf_assoc1 = assoc_f (runComb (reduce f) $ xin11) 
                                   ((runComb f) ((runComb (reduce f) $ xin121), 
                                                 (runComb (reduce f) $ xin122))) 
                                   (runComb (reduce f) $ xin2)
              prf_assoc2 = assoc_f (runComb (reduce f) $ xin121) 
                                   (runComb (reduce f) $ xin122)
                                   (runComb (reduce f) $ xin2)
              prf_assoc3 = sym $ assoc_f (runComb (reduce f) $ xin11) 
                                           (runComb (reduce f) $ xin121) 
                                           (runComb f $ ((runComb (reduce f) $ xin122), 
                                                         (runComb (reduce f) $ xin2)))
          in rewrite prf_prev in 
             rewrite prf_assoc1 in 
             rewrite prf_assoc2 in prf_assoc3
    balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=(ty1, ty2)} (AllP {ty1=ty1} {ty2=ty2} x y) f xin assoc_f unpack_prf | False | (RL _ _ _) = ?sym_lr
  balance_lemma_succ {aIsSig = aIsSig} k prev {a = a} {as=(ty1, ty2)} (AllP {ty1=ty1} {ty2=ty2} x y) f (xin1, xin2) assoc_f unpack_prf | True 
    = let prf1 = cong fst $ extSnd unpack_prf in 
      let prf2 = cong (fst . snd) $ extSnd unpack_prf in 
      rewrite prf2 in rewrite prf1 in Refl

balance_lemma: (k: Nat) -> {a:_} -> {as:_} -> {auto aIsSig: Sig a} 
  -> (allA: All (OfType a) as) 
  -> (f: Eval.Combinational (a, a) a) -> (xin: as)
  -> (assoc_f: assoc f)
  -> {as': _} -> {xin': _} -> {allA': All (OfType a) as'} -> {sigAs': Sig as'}
  -> (as' ** (xin', allA', sigAs')) 
  = balance {ty=a} {comb=Eval.Combinational} {max_iter=k} {asSig=allSig aIsSig allA} 
            (MkComb $ \x => xin) {shape=allA}
  -> (runComb (reduce {as=as} {prf2=allA} f) $ xin) = ((runComb $ app (reduce {prf2=allA'} f) xin') ())
balance_lemma 0 allA f xin assoc_f prf_unpack = balance_lemma_base allA f xin assoc_f prf_unpack
balance_lemma (S k) allA f xin assoc_f prf_unpack 
  = balance_lemma_succ k (balance_lemma k) allA f xin assoc_f prf_unpack

reduce_eq: {a:_} -> {as:_} -> {auto aIsSig: Sig a} -> (k: Nat)
  -> (allA: All (OfType a) as)
  -> (f: Eval.Combinational (a, a) a) 
  -> (xin: as)
  -> (assoc_f: assoc f)
  -> (runComb (reduce {as=as} {prf1=aIsSig} f) $ xin) 
   = (runComb (balancedReduce {max_iter=k} f) $ xin)
reduce_eq k allA f xin assoc_f with (balance {max_iter=k} {shape=allA} {comb=Eval.Combinational} (MkComb $ \x => xin)) proof prf_unpack
  reduce_eq k allA f xin assoc_f | (as' ** (xin', allA', sigAs')) 
    = balance_lemma k allA f xin assoc_f (sym $ prf_unpack)

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
