module Sym.CombP

import Data.Signal
import Data.BitVec

import Data.Nat
import Data.Signal

import Sym.Comb.Comb as CB
import Sym.Comb.CombPrimitive as CP


-- public export
data E: (Type -> Type -> Type) -> Type -> Type -> Type where
  F: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
   -> (E comb () a -> E comb () b) -> E comb a b
  P: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
    -> E comb () a -> E comb () b -> E comb () (a, b)
  C: comb a b -> E comb a b

toComb: (Comb comb, Primitive comb) 
  => {auto aIsSig: Sig a} 
  -> {auto bIsSig: Sig b} 
  -> E comb a b -> comb a b
toComb (F f) = 
  lam {aIsSig = aIsSig} {bIsSig=bIsSig} 
    $ \x => (toComb {bIsSig = bIsSig} . f) (C x)
toComb (P x y) = prod (toComb x) (toComb y)
toComb (C x) = x

public export
(Comb comb, Primitive comb) => Comb (E comb) where
  lam f = F f
  app (F f) p@(P x y) = f p
  app f@(F _) e = 
    C $ app {aIsSig = aIsSig} {bIsSig = bIsSig} 
          (toComb {aIsSig = aIsSig} {bIsSig = bIsSig} f) 
          (toComb {bIsSig = aIsSig} e)
  app (P x y) _ = P x y
  app (C f) x = C $ app f (toComb x)
  prod x y = P x y
  proj1 (P x y) = x
  proj1 x = C $ proj1 $ toComb x
  proj2 (P x y) = y
  proj2 x = C $ proj2 $ toComb x
  unit = C $ unit

(Comb comb, Primitive comb) => Primitive (E comb) where
  const = ?rc
  add x y = C $ add (toComb x) (toComb y)
  concat = ?con
  and = ?rand
  or = ?ror
  xor = ?rxor
  not = ?rnot
  slice l u x = C $ slice l u (toComb x)
  eq = ?req
  ltu = ?rltu
  lt = ?rlt
  mux21 = ?rmux
  shiftLL = ?rsll
  shiftRL = ?rsrl
  shiftRA = ?rsra


export
prodElim: (Comb comb, Primitive comb) 
  => {auto aIsSig: Sig a} 
  -> {auto bIsSig: Sig b} 
  -> (forall comb' . (Comb comb', Primitive comb') => comb' a b) 
  -> comb a b
prodElim x = toComb x
