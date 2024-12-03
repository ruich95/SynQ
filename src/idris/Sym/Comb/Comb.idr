module Sym.Comb.Comb

import Data.Signal
import Data.BitVec

public export
interface Comb (comb: Type -> Type -> Type) where
  lam: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
    -> (comb () a -> comb () b) -> comb a b
    
  app: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
    -> comb a b -> comb () a -> comb () b
  
  prod: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
     -> comb () a -> comb () b -> comb () (a, b)
     
  proj1: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
      -> comb () (a, b) -> comb () a
  
  proj2: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
      -> comb () (a, b) -> comb () b
      
  unit: comb () ()
      
    
