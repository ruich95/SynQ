module Misc.Proofs

import Data.Nat

%default total

export 
lteRefl: (n: Nat) -> LTE n n
lteRefl 0 = LTEZero
lteRefl (S k) = LTESucc (lteRefl k)

export
lteTrans: LTE m n -> LTE k m -> LTE k n
lteTrans LTEZero LTEZero = LTEZero
lteTrans (LTESucc x) LTEZero = LTEZero
lteTrans (LTESucc x) (LTESucc y) = LTESucc (lteTrans x y)

export
lteRelaxLeft
   : (m: Nat) -> (n: Nat) 
  -> LTE (S m) n
  -> LTE m n
lteRelaxLeft 0 n _ = LTEZero
lteRelaxLeft (S k) 0 prf = absurd prf
lteRelaxLeft (S k) (S j) (LTESucc prf) = 
  LTESucc $ lteRelaxLeft k j prf

export
lteRelaxRight
   : (m: Nat) -> (n: Nat) 
  -> LTE m n
  -> LTE m (S n)
lteRelaxRight 0 n prf = LTEZero
lteRelaxRight (S k) n prf = 
  LTESucc $ lteRelaxLeft k n prf

export
minusPreserveLTE
   : (m: Nat) -> (n: Nat) 
  -> LTE (m `minus` n) m
minusPreserveLTE m 0 = 
  rewrite minusZeroRight m
  in lteRefl m
minusPreserveLTE 0 (S k) = LTEZero
minusPreserveLTE (S j) (S k) = 
  let prf = minusPreserveLTE j k 
  in lteRelaxRight (j `minus` k) j prf

-- m <= n ==> (m - n) <= n
export
lteMinus: (m: Nat) -> (n: Nat) 
  -> LTE m n 
  -> LTE (n `minus` m) n
lteMinus 0 n _ = 
  rewrite minusZeroRight n 
  in lteRefl n
lteMinus (S k) (S n) (LTESucc prf) = 
  let prf1 = lteMinus k n prf
  in lteRelaxRight (n `minus` k) n prf1

export
eqPred: S m = S n -> m = n
eqPred Refl = Refl

export
{j:_} -> Uninhabited (LTE (S $ S j) (S j)) where
  uninhabited {j = 0} (LTESucc x) = uninhabited x
  uninhabited {j = (S k)} (LTESucc x) = uninhabited x

export
{j:_} -> Uninhabited (LTE (S $ S $ S j) (S j)) where
  uninhabited {j = 0} (LTESucc x) = absurd x
  uninhabited {j = (S k)} (LTESucc x) = absurd x
  
export
ltePlus: (n: Nat) -> LTE n (n+k)
ltePlus 0 = LTEZero
ltePlus (S j) = LTESucc $ ltePlus j
