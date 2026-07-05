||| Base module for bit vectors, which are non-empty sequences of bits (booleans).
module Data.BitVec.Base

public export infixl 7 <:

||| None-empty bit vectors, which is inductively defined by extending a bit vector of length `n` with a new least significant bit (LSB) on the right.
||| Example: MSB True <: False <: True <: True ==> 4b1011 
public export
data BitVec : Nat -> Type where
    MSB : Bool -> BitVec 1
    (<:) : (msbs : BitVec n) -> (lsb : Bool) -> BitVec (S n)

%name BitVec bv, bv1, bv2

||| A bit vector cannot be empty.
public export
Uninhabited (BitVec 0) where
  uninhabited (MSB _) impossible
  uninhabited (bv <: _) impossible

||| A functor like map function for bit vectors.
public export
map : (f : Bool -> Bool) -> (bs : BitVec n) -> BitVec n
map f (MSB b) = MSB (f b)
map f (bs <: b) = map f bs <: f b

||| A Zippable like zipWith function for bit vectors.
public export
zipWith : (f : Bool -> Bool -> Bool) -> (bs1 : BitVec n) -> (bs2 : BitVec n) -> BitVec n
zipWith f (MSB b1) (MSB b2) = MSB (f b1 b2)
zipWith f (bs1 <: b1) (bs2 <: b2) = zipWith f bs1 bs2 <: f b1 b2

||| Given a bit vector whose length `n` is of multiplicity 0 (is not accessible), intro a variable `len` and a proof that `len = n`. So that `n` can be accessed (via `len`) in the context of the caller.
public export
introLength : (bs : BitVec n) -> (len : Nat ** len = n)
introLength (MSB _) = (1 ** Refl)
introLength (bs <: _) =
  let (len ** prf) = introLength bs
  in (S len ** cong S prf)

||| Convert a bit vector of length `m` to a bit vector of length `n`, given a proof that `m = n`.
public export
convertWidth : (0 _: m = n) -> BitVec m -> BitVec n
convertWidth prf bs = rewrite sym prf in bs

||| Given a proof that `m = n`, converting a bit vector of length `m` to a bit vector of length `n` does not change the vector.
export
0 convertWidthId : (0 prf : m = n) -> (xs : BitVec m) -> convertWidth prf xs = xs
convertWidthId prf xs = rewrite prf in Refl