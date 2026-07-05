||| Structural operations on bit vectors (concatenation, spliting, slicing, etc.)
module Data.BitVec.StructuralOps

import Data.BitVec.Base
import Data.Nat
import Syntax.PreorderReasoning

||| Concatenate two bit vectors, with the first vector as MSBs and the second vector as LSBs.
||| Example: (MSB True <: False) ++ (MSB False <: True) ==> MSB True <: False <: False <: True
public export
(++) : BitVec m -> BitVec n -> BitVec (m + n)
(++) {n = 1} bs1 (MSB x) = convertWidth (plusCommutative 1 m) $ bs1 <: x
(++) {n = (S n)} bs1 (msbs <: lsb) = 
  convertWidth (plusCommutative (S n) m) 
    $ (convertWidth (plusCommutative m n) $ bs1 ++ msbs) <: lsb

||| Get LSBs of a bit vector until (exclusive) the `k`-th (0-indexed) bit.
public export
lsbsUntil : (k : Nat) 
  -> {auto prfLower : GT k 0} -> {auto prfUpper : LT k n}
  -> (bv : BitVec n) -> BitVec k
lsbsUntil 0 bv          = absurd prfLower
lsbsUntil (S k) (MSB x) = absurd prfUpper
lsbsUntil (S 0) (msbs <: lsb) = MSB lsb
lsbsUntil (S (S k)) {prfUpper = (LTESucc z)} (msbs <: lsb) = (lsbsUntil (S k) msbs) <: lsb

||| Get MSBs of a bit vector from (inclusive) the `k`-th (0-indexed) bit.
public export
msbsFrom : (k : Nat) 
  -> {auto prfUpper : LT k n}
  -> (bv : BitVec n) -> BitVec (n `minus` k)
msbsFrom 0 bv = convertWidth (sym $ minusZeroRight n) bv
msbsFrom (S k) (MSB x) = absurd prfUpper
msbsFrom {n = S n} (S k) {prfUpper = (LTESucc z)} (msbs <: lsb) = msbsFrom k msbs

||| Split a bit vector at the `k`-th (0-indexed) bit.
public export
splitAt : (k : Nat) 
  -> {auto prfLower : GT k 0} -> {auto prfUpper : LT k n}
  -> (bv : BitVec n) -> (BitVec k, BitVec (n `minus` k))
splitAt k bv = (lsbsUntil k bv, msbsFrom k bv)

||| Properties of structural operations on bit vectors.
namespace Properties
    %default total
    
    export
    0 
    concatLemma : (xs : BitVec m) -> (ys : BitVec n) -> (z : Bool)
        -> (convertWidth (sym (plusSuccRightSucc m n)) $ xs ++ (ys <: z)) = ((xs ++ ys) <: z)
    concatLemma xs ys z = rewrite plusCommutative n m in Refl

    export
    0 
    lsbsUntilLemma : (k : Nat) -> (msbs : BitVec n) -> (lsb : Bool) 
        -> (prfLower : GT k 0) -> (prfUpper : LT k n)
        -> (lsbsUntil (S k) {prfUpper = LTESucc prfUpper} (msbs <: lsb)) = ((lsbsUntil k msbs) <: lsb)
    lsbsUntilLemma 0 msbs lsb prfLower prfUpper = absurd prfLower
    lsbsUntilLemma (S k) msbs lsb (LTESucc LTEZero) prfUpper = Refl

    0
    lemma1 : (n : Nat) -> BitVec n -> LTE 1 n
    lemma1 1 (MSB x) = LTESucc LTEZero
    lemma1 (S n) (msbs <: lsb) = LTESucc LTEZero

    0
    lemma_plus_SS : (m, k : Nat) -> m + (S (S k)) = S (S (m + k))
    lemma_plus_SS m k = 
      Calc $ 
        |~ (m + (S (S k))) 
        ~~ S (S (k + m)) ...(plusCommutative m (S $ S k))
        ~~ S (S (m + k)) ...(rewrite plusCommutative k m in Refl)

    export
    0 
    concatPreserveMSBsLSBs : (m , n : Nat) -> (xs : BitVec m) -> (ys : BitVec n)
        -> (prfLower : GT n 0) -> (prfUpper : LT n (m + n))
        -> lsbsUntil n {prfLower = prfLower} {prfUpper = prfUpper} (xs ++ ys) = ys
    concatPreserveMSBsLSBs m 0 xs ys prfLower prfUpper = absurd (lemma1 0 ys)
    concatPreserveMSBsLSBs m (S 0) xs (MSB x) prfLower prfUpper = Refl
    concatPreserveMSBsLSBs m (S 0) xs (msbs <: lsb) prfLower prfUpper = absurd msbs
    concatPreserveMSBsLSBs m (S (S k)) xs (msbs <: lsb) prfLower prfUpper 
      with (replace {p = \t => LT (S (S k)) t} (lemma_plus_SS m k) prfUpper)
      concatPreserveMSBsLSBs m (S (S k)) xs (msbs <: lsb) prfLower prfUpper | (LTESucc (LTESucc z)) 
        = cong (\v => v <: lsb) 
            (concatPreserveMSBsLSBs m (S k) xs msbs (LTESucc LTEZero) 
              (replace {p = \t => LTE (S (S k)) t} (plusSuccRightSucc m k) (LTESucc z)))

    0 
    lemma_minus_add : (m, k : Nat) -> minus (m + k) k = m
    lemma_minus_add m 0 =
      trans (cong (\t => minus t 0) (plusZeroRightNeutral m))
            (minusZeroRight m)
    lemma_minus_add m (S k) =
      trans (cong (\t => minus t (S k)) (sym (plusSuccRightSucc m k)))
            (lemma_minus_add m k)

    0 
    lemma_minus_eq : (m, k : Nat) -> minus (m + (S k)) (S k) = minus (m + k) k
    lemma_minus_eq m k = trans (lemma_minus_add m (S k)) (sym (lemma_minus_add m k))

    export
    0 
    concatPreserveMSBs : (m , n : Nat) -> (xs : BitVec m) -> (ys : BitVec n)
        -> (prfUpper : LT n (m + n))
        -> msbsFrom n {prfUpper = prfUpper} (xs ++ ys) 
         = convertWidth (rewrite plusCommutative m n in sym (minusPlus {n=m} n)) xs
    concatPreserveMSBs m 0 xs ys prfUpper = absurd (lemma1 0 ys)
    concatPreserveMSBs m (S 0) xs (MSB x) prfUpper 
      with (replace {p = \t => LT 1 t} (sym (plusSuccRightSucc m 0)) prfUpper)
      concatPreserveMSBs m (S 0) xs (MSB x) prfUpper | (LTESucc z) = Refl
    concatPreserveMSBs m (S k) xs (msbs <: lsb) prfUpper 
      with (replace {p = \t => LT (S k) t} (sym (plusSuccRightSucc m k)) prfUpper)
      concatPreserveMSBs m (S k) xs (msbs <: lsb) prfUpper | (LTESucc z) = 
        rewrite lemma_minus_eq m k in
        concatPreserveMSBs m k xs msbs z
