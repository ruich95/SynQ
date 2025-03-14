module Data.Signal

import Data.BitVec

public export
data Sig: Type -> Type where
  U:Sig Unit
  P: Sig a -> Sig b -> Sig (a, b)
  BV: {n:_} -> Sig $ BitVec n

public export
data NotUnit: Type -> Type where
  NUnit: (prf: a = () -> Void) -> NotUnit a

%hint
export
bvNotUnit: {n: _} -> NotUnit (BitVec n)
bvNotUnit = NUnit (\x => case x of Refl impossible)

-- %hint
-- export
-- prodNotUnit: {n: _} -> {p1: NotUnit a} -> {p2: NotUnit b} -> NotUnit (a, b)

public export
OfType: Type -> Type -> Type
OfType x y = x = y

fromOfType: {auto prf: OfType ty a} -> a -> ty
fromOfType x = rewrite prf in x

public export
data All: (pred: Type -> Type) -> Type -> Type where
  AllU: {0 pred: _} -> {x: Type} -> (pred x) -> All pred x
  AllP: {0 pred: _} -> All pred a -> All pred b -> All pred (a, b)

-- Example about using predicates All and OfType
exampleAllOfType: All (OfType (Nat, Nat)) (((Nat, Nat), (Nat, Nat)), (Nat, Nat))
exampleAllOfType = AllP (AllP (AllU Refl) (AllU Refl)) (AllU Refl)

%hint
export
allSig: Sig a -> All (OfType a) as -> Sig as
allSig prf_a (AllU prf) = 
  rewrite sym $ prf in prf_a
allSig prf_a (AllP p1 p2) = 
  P (allSig prf_a p1)
    (allSig prf_a p2)


