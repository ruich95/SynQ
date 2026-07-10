||| Base module for bit vectors, which are non-empty sequences of bits (booleans).
module Data.BitVec.Base

%default total

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

namespace Properties
  ||| Given a proof that `m = n`, converting a bit vector of length `m` to a bit vector of length `n` does not change the vector.
  export
  0 
  convertWidthId : (0 prf : m = n) -> (xs : BitVec m) -> convertWidth prf xs = xs
  convertWidthId prf xs = rewrite prf in Refl