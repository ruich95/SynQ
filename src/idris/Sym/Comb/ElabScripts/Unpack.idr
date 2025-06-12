module Sym.Comb.ElabScripts.Unpack

import Sym.Comb.CombPrimitive
import Language.Reflection
import Data.Nat
import Data.Vect
import Data.BitVec

%language ElabReflection

0 lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

-- %hint
lteRefl: {n:Nat} -> LTE n n
lteRefl {n=0} = LTEZero
lteRefl {n=(S k)} = LTESucc (lteRefl)

0 minusZero: (n:Nat) -> n = minus n 0
minusZero 0 = Refl
minusZero (S k) = Refl

0 minusSucc: (n:Nat) -> 1 = minus (S n) n
minusSucc 0 = Refl
minusSucc (S k) = (minusSucc k)
    
public export
unpack: (Primitive comb)
  => {n:_} -> Elab $ comb () (BitVec n) -> Vect n (comb () $ BitVec 1)
unpack = lambda _ $ \x => unpack' x (ns n n {prf=lteRefl})
where
  ns: (k: Nat) -> (n: Nat) 
   -> {prf: LTE n k} 
   ->  Vect n (m: Nat ** LTE (S m) k)
  ns k 0 {prf} = []
  ns k (S m) {prf} = (m ** prf) :: ns k m {prf = lteSuccLeft prf}

  take: {m:_} -> (k: Nat) 
     -> {0 prf: LTE (S k) m}
     -> comb () (BitVec m)
     -> comb () (BitVec 1)
  take 0 {prf} x = slice 0 1 x
  take (S k) {prf} x = 
    rewrite minusSucc k 
    in slice {n=m} {prf_lower=lteSucc $ S k} {prf_upper=prf} (S k) (S $ S k) x
      
  unpack': {z:_} -> comb () (BitVec z)
    -> Vect k (m: Nat ** LTE (S m) z) 
    -> Elab $ Vect k (comb () $ BitVec 1)
  unpack' x [] = pure []
  unpack' x ((i ** prf_i) :: is) = 
    do ys <- (unpack' x is)
       pure (take i {prf=prf_i} x :: ys)
 
