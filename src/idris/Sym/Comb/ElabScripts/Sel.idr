module Sym.Comb.ElabScripts.Sel

import Sym.Comb.CombPrimitive
import Language.Reflection
import Data.Nat
import Data.Vect
import Data.List1

import Data.BitVec
import Data.Signal
import Sym.Comb.ElabScripts.Unpack

lemma: (x:Nat) -> (y: Nat) -> LTE x y 
  -> (z:Nat ** (x + z) = y)
lemma 0 y LTEZero = (y ** Refl)
lemma (S x) (S y) (LTESucc p) = 
  let (z ** prf) = lemma x y p 
  in (z ** cong S prf)

split: {m:_} -> Vect (m + n) a -> (Vect m a, Vect n a)
split {m = 0} xs = ([], xs)
split {m = (S k)} (x :: xs) = 
  let (xs', ys) = split xs 
  in (x :: xs', ys)

split': (m:_) -> Vect (m + n) a -> Elab $ (Vect m a, Vect n a)
split' 0 xs = pure ([], xs)
split' (S k) (x :: xs) = 
  do (xs', ys) <- split' k xs
     pure $ (x::xs', ys)

lemma3: (k: Nat) -> (n:Nat) -> LTE 1 n -> LTE 1 (n + k)
lemma3 0 n x = rewrite plusZeroRightNeutral n in x
lemma3 (S k) n x = rewrite plusCommutative n (S k) in LTESucc LTEZero

lemma2: (n:Nat) -> LTE 1 (power 2 n)
lemma2 0 = LTESucc LTEZero
lemma2 (S j) = 
  let prf = lemma2 j 
  in lemma3 ((power 2 j)+0) (power 2 j) prf

selGen': (Primitive comb)
  => (idxWidth : Nat)
  -> (dataWidth: Nat)
  -> (numInputs: Nat)
  -> {auto 0 p: LTE 1 numInputs}
  -> (Vect numInputs $ comb () (BitVec dataWidth))
  -> (Vect idxWidth $ comb () (BitVec 1))
  -> Elab $ comb () (BitVec dataWidth)
selGen' 0 dataWidth 0 {p = p} impossible
selGen' 0 dataWidth (S k) {p = p} (x::xs) _ = pure $ x
selGen' (S 0) dataWidth 0 {p=p} impossible
selGen' (S 0) dataWidth (S 0) {p=p} (x::xs) _ = pure $ x
selGen' (S 0) dataWidth (S (S k)) {p=p} (x1::x2::_) (i::_) = pure $ mux21 i x2 x1
selGen' (S (S k)) dataWidth numInputs xs is with (power 2 (S k)) proof prf1
  selGen' (S (S k)) dataWidth numInputs xs (i::is) | partLen with (partLen `lte` numInputs) proof prf
    selGen' (S (S k)) dataWidth numInputs xs (i::is) | partLen | False = 
      (selGen' (S k) dataWidth numInputs) xs is
    selGen' (S (S k)) dataWidth numInputs xs (i::is) | partLen | True = 
      let prf = lteReflectsLTE partLen numInputs prf 
          p1: LTE 1 partLen = rewrite sym $ prf1 in lemma2 (S k) 
          (restLen ** prf) = lemma partLen numInputs prf
          (xs1, xs2) = split {m=partLen} {n=restLen} (rewrite prf in xs)
      in case restLen of 
           0 => (selGen' {comb=comb} (S k) dataWidth numInputs) xs is
           (S j) => do t1 <- (selGen' {comb=comb} (S k) dataWidth partLen) xs1 is
                       t2 <- (selGen' {comb=comb} (S k) dataWidth (S j)) xs2 is
                       pure $ mux21 i t2 t1

%language ElabReflection

sel: (Primitive comb) => 
  (Vect 8 $ comb () (BitVec 8)) -> (Vect 3 $ comb () (BitVec 1)) -> Elab $ comb () (BitVec 8)
sel xs idx = selGen' 3 8 8 xs idx

t: Vect 1 a -> Vect 0 a
-- t = %runElab tl

Repeated: Nat -> Type -> Type
Repeated 0 t = ()
Repeated 1 t = t
Repeated (S $ S k) t = (t, Repeated (S k) t)

repeatLemma: (n:_) -> (aIsSig: Sig a) -> Sig (Repeated n a)
repeatLemma 0 aIsSig = U
repeatLemma (S 0) aIsSig = aIsSig
repeatLemma (S (S k)) aIsSig = P aIsSig (repeatLemma (S k) aIsSig)
