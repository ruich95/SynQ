module Data.BitVec.ArithmeticOps

import Data.BitVec.Base
import Data.BitVec.StructuralOps
import Data.Nat

ones : (n : Nat) -> {auto prf : GT n 0} -> BitVec n
ones 0  {prf} = absurd prf
ones (S 0) = MSB True
ones (S (S k)) {prf = (LTESucc x)} = ones (S k) <: True

zeros : (n : Nat) -> {auto prf : GT n 0} -> BitVec n
zeros 0  {prf} = absurd prf
zeros (S 0) = MSB False
zeros (S (S k)) {prf = (LTESucc x)} = zeros (S k) <: False

and : (bs1 : BitVec n) -> (bs2 : BitVec n) -> BitVec n
and = zipWith (\x, y => x && y)

or : (bs1 : BitVec n) -> (bs2 : BitVec n) -> BitVec n
or = zipWith (\x, y => x || y)

not : (bs : BitVec n) -> BitVec n
not = map not

xor : (bs1 : BitVec n) -> (bs2 : BitVec n) -> BitVec n
xor = zipWith (\x, y => x /= y)

export
lteRefl : (n : Nat) -> LTE n n
lteRefl 0 = LTEZero
lteRefl (S k) = LTESucc (lteRefl k)

carry : {0 r :_ } -> (p : BitVec n) -> (g : BitVec n) -> (carryIn : BitVec 1) -> (k : BitVec n -> r) -> r
carry p@(MSB x) g@(MSB y) carryIn k = k $ g `or` (carryIn `and` p)
carry (MSB x) (msbs <: lsb) carryIn k impossible
carry (msbs <: lsb) (MSB x) carryIn k impossible
carry (p <: lsbP) (g <: lsbG) (MSB carryIn) k = 
    let c = (lsbG || (carryIn && lsbP))
    in carry p g (MSB c) (\bs => k (bs <: c))


fullAdd : (carryIn : BitVec 1) -> (bs1 : BitVec n) -> (bs2 : BitVec n) -> (BitVec 1, BitVec n)
fullAdd (MSB carryIn) (MSB y) (msbs <: lsb) impossible
fullAdd (MSB carryIn) (msbs <: lsb) (MSB y) impossible
fullAdd (msbs <: lsb) bs1 bs2 = absurd msbs
fullAdd (MSB carryIn) (MSB x) (MSB y) = 
  (MSB $ (x && y) || (carryIn && (x /= y)), MSB (carryIn /= (x /= y)))
fullAdd (MSB carryIn) bv1@(msbs1 <: lsb1) bv2@(msbs2 <: lsb2) with (introLength bv1)
  fullAdd (MSB carryIn) bv1@(msbs1 <: lsb1) bv2@(msbs2 <: lsb2) | ((S k) ** Refl) =
    let p    = bv1 `xor` bv2
        g    = bv1 `and` bv2
        c    = carry p g (MSB carryIn) (\bs => bs) <: carryIn
        cOut = convertWidth (sym (minusOneSuccN k))
              $ msbsFrom (S k) {prfUpper = lteRefl (S (S k))} c
        cs   = lsbsUntil (S k) {prfUpper = lteRefl (S (S k))} c
        sum  = p `xor` cs
    in (cOut, sum)

add : (bs1 : BitVec n) -> (bs2 : BitVec n) -> (BitVec n)
add bs1 bs2 = snd $ fullAdd (MSB False) bs1 bs2

namespace Properties
  carry : (p : BitVec n) -> (g : BitVec n) -> (carryIn : BitVec 1) -> BitVec n
  carry p@(MSB x) g@(MSB y) carryIn = g `or` (carryIn `and` p)
  carry (MSB x) (msbs <: lsb) carryIn impossible
  carry (msbs <: lsb) (MSB x) carryIn impossible
  carry (p <: lsbP) (g <: lsbG) (MSB carryIn) = 
      let c = (lsbG || (carryIn && lsbP))
      in carry p g (MSB c) <: c
  
  0
  carryCPSLemma : (p : BitVec n) -> (g : BitVec n) -> (carryIn : BitVec 1) -> (k : BitVec n -> r)
    -> ArithmeticOps.carry p g carryIn k = k (Properties.carry p g carryIn)
  carryCPSLemma (MSB x) (MSB y) carryIn k = Refl
  carryCPSLemma (MSB x) (msbs <: lsb) carryIn k = absurd msbs
  carryCPSLemma (msbs <: lsb) (MSB x) carryIn k = absurd msbs
  carryCPSLemma (msbs <: lsb) (bv <: x) (MSB y) k = 
      carryCPSLemma msbs bv (MSB (x || (y && lsb))) (\bs => k (bs <: (x || (y && lsb))))
  carryCPSLemma (msbs <: lsb) (bv <: x) (bv1 <: y) k = absurd bv1

  0
  prf: (p : BitVec n) -> (g : BitVec n) -> (carryIn : BitVec 1) 
    -> (Properties.carry p g carryIn) = ArithmeticOps.carry p g carryIn (\x => x)
  prf p g carryIn = sym $ carryCPSLemma p g carryIn (\x => x)

  fullAddLemma : (carryIn : BitVec 1) 
    -> (bv1LSBs : BitVec n) -> (bv2LSBs : BitVec n) 
    -> (bv1MSBs : BitVec m) -> (bv2MSBs : BitVec m) 
    -> (fullAdd carryIn (bv1MSBs ++ bv1LSBs) (bv2MSBs ++ bv2LSBs))
     = (let (cOutLower, sumLower) = fullAdd carryIn bv1LSBs bv2LSBs in
        let (cOutUpper, sumUpper) = fullAdd cOutLower bv1MSBs bv2MSBs in
        (cOutUpper, sumUpper ++ sumLower))   
  fullAddLemma carryIn bv1LSBs bv2LSBs bv1MSBs bv2MSBs = ?fullAddLemma_rhs
