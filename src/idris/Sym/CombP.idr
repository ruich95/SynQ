module Sym.CombP

import Data.Signal
import Data.BitVec

import Data.Nat
import Data.Signal

import Sym.Comb.Comb as CB
import Sym.Comb.CombPrimitive as CP


public export
data E: (Type -> Type -> Type) -> Type -> Type -> Type where
  F: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
   -> (E comb () a -> E comb () b) -> E comb a b
  P: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
    -> E comb () a -> E comb () b -> E comb () (a, b)
  C: comb a b -> E comb a b

public export
toComb: (Comb comb) 
  => {auto aIsSig: Sig a} 
  -> {auto bIsSig: Sig b} 
  -> E comb a b -> comb a b
toComb (F f) = 
  lam {aIsSig = aIsSig} {bIsSig=bIsSig} 
    $ \x => (toComb {bIsSig = bIsSig} . f) (C x)
toComb (P x y) = prod (toComb x) (toComb y)
toComb (C x) = x

public export
(Comb comb) => Comb (E comb) where
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

public export
(Comb comb, Primitive comb) => Primitive (E comb) where
  const x = C $ const x
  add x y = C $ add (toComb x) (toComb y)
  concat x y = C $ concat (toComb x) (toComb y)
  and x y = C $ and (toComb x) (toComb y)
  or x y = C $ or (toComb x) (toComb y)
  xor x y = C $ xor (toComb x) (toComb y)
  not x = C $ not (toComb x)
  slice l u x = C $ slice l u (toComb x)
  eq x y = C $ eq (toComb x) (toComb y)
  ltu x y = C $ ltu (toComb x) (toComb y)
  lt x y = C $ lt (toComb x) (toComb y)
  mux21 b x y = C $ mux21 (toComb b) (toComb x) (toComb y)
  shiftLL k x = C $ shiftLL k (toComb x)
  shiftRL k x = C $ shiftRL k (toComb x)
  shiftRA k x = C $ shiftRA k (toComb x)


export
prodElim: (Comb comb, Primitive comb) 
  => {auto aIsSig: Sig a} 
  -> {auto bIsSig: Sig b} 
  -> (forall comb' . (Comb comb', Primitive comb') => comb' a b) 
  -> comb a b
prodElim x = toComb x
