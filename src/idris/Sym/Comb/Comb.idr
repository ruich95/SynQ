module Sym.Comb.Comb

import Data.Signal
import Data.BitVec

public export
interface Comb (0 comb: Type -> Type -> Type) where
  lam: {auto 0 aIsSig: Sig a} -> {auto 0 bIsSig: Sig b}
    -> (comb () a -> comb () b) -> comb a b
    
  app: {auto 0 aIsSig: Sig a} -> {auto 0 bIsSig: Sig b}
    -> comb a b -> comb () a -> comb () b
  
  prod: {auto 0 aIsSig: Sig a} -> {auto 0 bIsSig: Sig b}
     -> comb () a -> comb () b -> comb () (a, b)
     
  proj1: {auto 0 aIsSig: Sig a} -> {auto 0 bIsSig: Sig b}
      -> comb () (a, b) -> comb () a
  
  proj2: {auto 0 aIsSig: Sig a} -> {auto 0 bIsSig: Sig b}
      -> comb () (a, b) -> comb () b
      
  unit: comb () ()
      
    
