module Sym.Comb.ElabScripts.Sel

import Sym.Comb.Comb
import Sym.Comb.CombPrimitive
import Language.Reflection
import Data.Nat
import Data.Vect
import Data.List1

import Data.BitVec
import Data.Signal
import Sym.Comb.ElabScripts.Unpack
import Sym.Comb.ElabScripts.RepeatUtil

lemma': (x:Nat) -> (y: Nat) -> (0 _: LTE x y)
  -> x + (minus y x) = y
lemma' 0 y LTEZero = minusZeroRight y
lemma' (S x) (S y) (LTESucc z) = cong S $ lemma' x y z

lemma: (x:Nat) -> (y: Nat) -> (0 _: LTE x y)
  -> (z:Nat ** (x + z) = y)
lemma x y z = (minus y x ** lemma' x y z)

-- lemma 0 y LTEZero = (y ** Refl)
-- lemma (S x) (S y) (LTESucc p) = 
--   let (z ** prf) = lemma x y p 
--   in (z ** cong S prf)

-- split: {m:_} -> Vect (m + n) a -> (Vect m a, Vect n a)
-- split {m = 0} xs = ([], xs)
-- split {m = (S k)} (x :: xs) = 
--   let (xs', ys) = split xs 
--   in (x :: xs', ys)

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

selGen': (Comb comb, Primitive comb)
  => (idxWidth : Nat)
  -> (dataWidth: Nat)
  -> (numInputs: Nat)
  -> {auto 0 p: LTE 1 numInputs}
  -> (Vect idxWidth $ comb () (BitVec 1))
  -> (Vect numInputs $ comb () (BitVec dataWidth))
  -> Elab $ comb () (BitVec dataWidth)
selGen' 0 dataWidth (S n) {p = (LTESucc p)} is (x::_) = pure x
selGen' (S k) dataWidth (S n) {p = (LTESucc p)} is xs with (power 2 k) proof prf1
  selGen' (S k) dataWidth (S n) {p = (LTESucc p)} is xs | partLen with (partLen `lte` (S n)) proof prf2
    selGen' (S k) dataWidth (S n) {p = (LTESucc p)} (i::is) xs | partLen | False = 
      selGen' k dataWidth (S n) is xs
    selGen' (S k) dataWidth (S n) {p = (LTESucc p)} (i::is) xs | partLen | True = 
      let prf2 = lteReflectsLTE partLen (S n) prf2 
          p1: LTE 1 partLen = rewrite sym $ prf1 in lemma2 k 
          (restLen ** prf2) = lemma partLen (S n) prf2
      in case restLen of 
           0 => selGen' k dataWidth (S n) is xs
           (S j) => do (xs1, xs2) <- split' partLen {n=restLen} (rewrite prf2 in xs)
                       t1 <- (selGen' k dataWidth partLen is xs1)
                       t2 <- (selGen' k dataWidth (S j) is xs2)
                       pure $ mux21 i t2 t1

selGen: (Comb comb, Primitive comb)
  => {auto idxWidth : Nat}
  -> {auto dataWidth: Nat}
  -> {auto numInputs: Nat}
  -> {auto 0 p: LTE 1 numInputs}
  -> Elab $ (comb () $ Repeat numInputs (BitVec dataWidth))
         -> (comb () $ BitVec idxWidth)
         -> comb () (BitVec dataWidth)                  
selGen = lambda _ $ \xs => lambda _ $ \is => 
  do is <- Unpack.unpack {n=idxWidth} <*> pure is
     xs <- unpackV <*> pure xs
     (selGen' idxWidth dataWidth numInputs is xs)

%language ElabReflection

sel: (Comb comb, Primitive comb)
  => comb () (Repeat 8 $ BitVec 8) -> comb () (BitVec 3) 
  -> comb () (BitVec 8)
sel = %runElab selGen {idxWidth=3} {dataWidth=8} {numInputs=8}
