module Data.BitVec

import Data.Bool
import Data.Nat
import Prelude

public export infixl 7 <+


||| None-empty bit vectors from left to right, with the most significant bit (MSB) on the left and the least significant bit (lsb) on the right.
||| Example: MSB True <+ False <+ True <+ True ==> 4b1011 
data BitVec : Nat -> Type where
    MSB : Bool -> BitVec 1
    (<+) : (msbs : BitVec n) -> (lsb : Bool) -> BitVec (S n)

%name BitVec bs, bs1, bs2

length : (bs : BitVec n) -> Nat
length (MSB _) = 1
length (bs <+ _) = S (length bs)

||| Given a bit vector whose length `n` is of multiplicity 0 (is not accessible), intro a variable `len` and a proof that `len = n`. So that `n` can be accessed (via `len`) in the context of the caller.
introLength : (bs : BitVec n) -> (len : Nat ** len = n)
introLength (MSB _) = (1 ** Refl)
introLength (bs <+ _) =
  let (len ** prf) = introLength bs
  in (S len ** cong S prf)


||| Concatenate two bit vectors, with the first vector as MSBs and the second vector as LSBs.
||| Example: (MSB True <+ False) ++ (MSB False <+ True) ==> MSB True <+ False <+ False <+ True

||| LTE (S n) 0 is impossible
lteSuccZeroVoid : LTE (S n) 0 -> Void
lteSuccZeroVoid LTEZero impossible
lteSuccZeroVoid (LTESucc _) impossible

||| BitVec 0 is uninhabited
bitVec0Void : BitVec 0 -> Void
bitVec0Void (MSB _) impossible
bitVec0Void (_ <+ _) impossible

||| Prepend a boolean as the new MSB to a bit vector
consMSB : Bool -> BitVec n -> BitVec (S n)
consMSB b (MSB y) = MSB b <+ y
consMSB b (bs <+ y) = (consMSB b bs) <+ y

||| Helper for ++ that works with explicit (non-erased) lengths
concatGo : (a, b : Nat) -> BitVec a -> BitVec b -> BitVec (a + b)
concatGo 1 b (MSB x) bs = consMSB x bs
concatGo (S k) b (msbs <+ lsb) bs = replace {p = BitVec} (sym (plusSuccRightSucc k b)) (concatGo k (S b) msbs (consMSB lsb bs))

(++) : BitVec m -> BitVec n -> BitVec (m + n)
(++) bs1 bs2 = 
  let (m' ** prf1) = introLength bs1
      (n' ** prf2) = introLength bs2
      bs1' : BitVec m'
      bs1' = replace {p = BitVec} (sym prf1) bs1
      bs2' : BitVec n'
      bs2' = replace {p = BitVec} (sym prf2) bs2
      result : BitVec (m' + n')
      result = concatGo m' n' bs1' bs2'
  in replace {p = \k => BitVec k} (cong2 (+) prf1 prf2) result

checkConcat: (MSB True <+ False) ++ (MSB False <+ True) = MSB True <+ False <+ False <+ True
checkConcat = Refl

||| Slice a bit vector from (lsb-indexed) `lower` to (lsb-indexed) `upper`, where `lower` is inclusive and `upper` is exclusive. The result is a new bit vector of length `upper - lower`.
||| Example: slice 1 3 prf1 prf2 (MSB True <+ False <+ True <+ True) ==> MSB False <+ True
slice : (lower : Nat) -> (upper : Nat) 
     -> (prf1 : LT lower upper) -> (prf2 : LTE upper n)
     -> (bs : BitVec n) -> BitVec (upper `minus` lower)
slice 0 1 (LTESucc LTEZero) (LTESucc LTEZero) (MSB x) = MSB x
slice 0 1 (LTESucc LTEZero) (LTESucc LTEZero) (msbs <+ lsb) = MSB lsb
slice 0 (S (S k)) (LTESucc LTEZero) (LTESucc w) (msbs <+ lsb) = 
  (slice 0 (S k) (LTESucc LTEZero) w msbs) <+ lsb
slice (S l) (S k) (LTESucc y) (LTESucc w) (msbs <+ lsb) = slice l k y w msbs
slice (S l) (S k) (LTESucc y) (LTESucc w) (MSB x) = case w of LTEZero => absurd (lteSuccZeroVoid y)

checkSlice: slice 1 3 (LTESucc (LTESucc LTEZero)) (LTESucc (LTESucc (LTESucc LTEZero))) (MSB True <+ False <+ True <+ True) = MSB False <+ True
checkSlice = Refl

||| LTE is reflexive
lteRefl : (k : Nat) -> LTE k k
lteRefl 0 = LTEZero
lteRefl (S k) = LTESucc (lteRefl k)

||| n + 1 = S n
plus_n_1_eq_S_n : (n : Nat) -> n + 1 = S n
plus_n_1_eq_S_n n = trans (plusCommutative n 1) (plusOneSucc n)

||| MSB x ++ ys = consMSB x ys
msbPlusEqConsMSB : (x : Bool) -> (ys : BitVec n) -> MSB x ++ ys = consMSB x ys
msbPlusEqConsMSB x (MSB y) = Refl
msbPlusEqConsMSB x (msbs <+ lsb) = 
  let (len ** prf) = introLength msbs
      ih = msbPlusEqConsMSB x msbs
  in ?msbPlusEqConsMSB_rhs_1

||| slice 0 n of (consMSB x ys) is ys
sliceZeroConsMSB : (n : Nat) -> (x : Bool) -> (ys : BitVec n)
  -> (prf1 : LT 0 n) -> (prf2 : LTE n (S n))
  -> replace {p = BitVec} (minusZeroRight n) (slice 0 n prf1 prf2 (consMSB x ys)) = ys
sliceZeroConsMSB 0 x ys prf1 prf2 = absurd (lteSuccZeroVoid prf1)
sliceZeroConsMSB (S 0) x (MSB y) (LTESucc LTEZero) (LTESucc LTEZero) = Refl
sliceZeroConsMSB (S (S k)) x (msbs <+ lsb) (LTESucc LTEZero) (LTESucc (LTESucc y)) = 
  let ih = sliceZeroConsMSB (S k) x msbs (LTESucc LTEZero) (LTESucc y)
  in cong (\v => v <+ lsb) ih

||| slice 0 n of (concatGo m n xs ys) is ys
sliceZeroConcatGo : (m, n : Nat) -> (xs : BitVec m) -> (ys : BitVec n)
  -> (prf1 : LT 0 n) -> (prf2 : LTE n (m + n))
  -> replace {p = BitVec} (minusZeroRight n) (slice 0 n prf1 prf2 (concatGo m n xs ys)) = ys
sliceZeroConcatGo 1 n (MSB x) ys prf1 prf2 = sliceZeroConsMSB n x ys prf1 prf2
sliceZeroConcatGo (S k) (S right) (msbs <+ lsb) ys (LTESucc LTEZero) (LTESucc y) with (concatGo (S k) (S right) (msbs <+ lsb) ys) proof p
  sliceZeroConcatGo (S k) (S right) (msbs <+ lsb) ys (LTESucc LTEZero) (LTESucc y) | result = ?sliceZeroConcatGo_rhs_1

||| slice n (S n) of (consMSB x ys) is MSB x
sliceNConsMSB : (n : Nat) -> (x : Bool) -> (ys : BitVec n)
  -> (prf1 : LT n (S n)) -> (prf2 : LTE (S n) (S n))
  -> replace {p = BitVec} (sym (minusOneSuccN n)) (slice n (S n) prf1 prf2 (consMSB x ys)) = MSB x
sliceNConsMSB 0 x ys prf1 prf2 = absurd (bitVec0Void ys)
sliceNConsMSB (S 0) x (MSB y) (LTESucc (LTESucc LTEZero)) (LTESucc (LTESucc LTEZero)) = Refl
sliceNConsMSB (S (S k)) x (msbs <+ lsb) (LTESucc (LTESucc (LTESucc y))) (LTESucc z) = sliceNConsMSB (S k) x msbs (LTESucc (LTESucc y)) z

||| slice n (m + n) of (concatGo m n xs ys) is xs
sliceNConcatGo : (m, n : Nat) -> (xs : BitVec m) -> (ys : BitVec n)
  -> (prf1 : LT n (m + n)) -> (prf2 : LTE (m + n) (m + n))
  -> replace {p = BitVec} (rewrite plusCommutative m n in minusPlus n) (slice n (m + n) prf1 prf2 (concatGo m n xs ys)) = xs
sliceNConcatGo 1 n (MSB x) ys prf1 prf2 = sliceNConsMSB n x ys prf1 prf2
sliceNConcatGo (S k) n (msbs <+ lsb) ys prf1 prf2 = ?sliceNConcatGo_rhs_1

0 propSliceConcat1 : (m , n : Nat) -> (xs : BitVec m) -> (ys : BitVec n)
    -> (prf1 : LT 0 n) -> (prf2 : LTE n (m + n))
    -> slice 0 n prf1 prf2 (xs ++ ys)
     = (rewrite the (minus n 0 = n) (minusZeroRight n) in ys)
propSliceConcat1 1 1 (MSB x) (MSB y) (LTESucc LTEZero) (LTESucc LTEZero) = Refl
propSliceConcat1 1 1 (MSB x) (msbs <+ lsb) (LTESucc LTEZero) (LTESucc LTEZero) = absurd (bitVec0Void msbs)
propSliceConcat1 1 (S (S right)) (MSB x) ys (LTESucc LTEZero) (LTESucc (LTESucc y)) = ?propSliceConcat1_rhs_0
propSliceConcat1 (S k) n (msbs <+ lsb) ys prf1 prf2 = ?propSliceConcat1_rhs_1

0 propSliceConcat2 : (m , n : Nat) -> (xs : BitVec m) -> (ys : BitVec n)
    -> (prf1 : LT n (m + n)) -> (prf2 : LTE (m + n) (m + n))
    -> slice n (m + n) prf1 prf2 (xs ++ ys)
     = (rewrite the (minus (m + n) n = m) (rewrite plusCommutative m n in minusPlus n) in xs)
propSliceConcat2 1 0 (MSB x) ys (LTESucc y) (LTESucc z) = absurd (bitVec0Void ys)
propSliceConcat2 1 (S k) (MSB x) ys (LTESucc (LTESucc y)) (LTESucc z) = ?propSliceConcat2_rhs_0
propSliceConcat2 (S k) n (msbs <+ lsb) ys prf1 prf2 = ?propSliceConcat2_rhs_1

||| Print a bit vector as a string of 0s and 1s with length, e.g. 4b1011
printB : BitVec n -> String
printB bs = show (length bs) ++ "b" ++ toBinary bs
  where
    toBinary : BitVec m -> String
    toBinary (MSB b) = if b then "1" else "0"
    toBinary (bs <+ b) = toBinary bs ++ if b then "1" else "0"
  