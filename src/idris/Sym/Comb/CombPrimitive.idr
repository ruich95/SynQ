module Sym.Comb.CombPrimitive

import Data.Signal
import Data.BitVec
import Data.Nat

public export
interface Primitive (0 comb: Type -> Type -> Type) where
  const: {n: Nat} -> BitVec n -> comb () (BitVec n)
  
  add: {n: Nat} -> comb () (BitVec n) -> comb () (BitVec n)
    -> comb () (BitVec $ S n)
    
  concat: {m:_} -> {n:_} 
       -> comb () (BitVec m) -> comb () (BitVec n) 
       -> comb () (BitVec $ m + n)
  
  not: {n:_} -> comb () (BitVec n) -> comb () (BitVec n) 
    
  and: {n:_} -> comb () (BitVec n) -> comb () (BitVec n) 
    -> comb () (BitVec n)
  
  or: {n:_} -> comb () (BitVec n) -> comb () (BitVec n) 
    -> comb () (BitVec n)
  
  xor: {n:_} -> comb () (BitVec n) -> comb () (BitVec n) 
    -> comb () (BitVec n)
                          
  slice: {n: Nat} -> (lower: Nat) -> (upper: Nat) 
      -> {auto 0 prf_upper: LTE upper n}
      -> {auto 0 prf_lower: LTE lower upper}
      -> comb () (BitVec n) -> comb () (BitVec $ minus upper lower)
  
  eq: {n: Nat} -> comb () (BitVec n) -> comb () (BitVec n)
    -> comb () (BitVec 1)
    
  ltu: {n: Nat} -> comb () (BitVec n) -> comb () (BitVec n)
    -> comb () (BitVec 1)
    
  lt: {n: Nat} -> comb () (BitVec n) -> comb () (BitVec n)
    -> comb () (BitVec 1)
    
  mux21: {n: Nat} -> comb () (BitVec 1) 
      -> comb () (BitVec n) -> comb () (BitVec n)
      -> comb () (BitVec n)
      
  shiftLL: {n:_} -> (sht: Nat) 
    -> comb () (BitVec n) -> comb () (BitVec n)

  shiftRL: {n:_} -> (sht: Nat) 
    -> comb () (BitVec n) -> comb () (BitVec n)
    
  shiftRA: {n:_} -> (sht: Nat) 
    -> comb () (BitVec n) -> comb () (BitVec n)
