module Data.Signal

import Data.BitVec
import Data.Vect

public export
data Sig: Type -> Type where
  U:Sig Unit
  P: Sig a -> Sig b -> Sig (a, b)
  BV: {n:_} -> Sig $ BitVec n
      
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

public export
Repeat: Nat -> Type -> Type
Repeat 0 t = ()
Repeat 1 t = t
Repeat (S $ S k) t = (t, Repeat (S k) t)

export
repeatSig: (n:_) -> (aIsSig: Sig a) -> Sig (Repeat n a)
repeatSig 0 aIsSig = U
repeatSig (S 0) aIsSig = aIsSig
repeatSig (S (S k)) aIsSig = P aIsSig (repeatSig (S k) aIsSig)

export
repeatRestSig: (n:_) -> Sig (Repeat (S n) a) -> Sig (Repeat n a)
repeatRestSig 0 p = U
repeatRestSig (S k) (P x y) = y

public export
repeatPack: {k:_} -> (a, Repeat k a) -> Repeat (S k) a
repeatPack {k = 0} x = fst x
repeatPack {k = (S k)} x = x

public export
repeatUnpack: {k:_} -> Repeat (S k) a -> (a, Repeat k a)
repeatUnpack {k = 0} x = (x, ())
repeatUnpack {k = (S k)} xs = xs

public export
fromVect: Vect n a -> Repeat n a
fromVect [] = ()
fromVect (x :: []) = x
fromVect (x :: (y :: xs)) = (x, fromVect (y :: xs))
