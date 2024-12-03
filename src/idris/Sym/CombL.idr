module Sym.CombL

import Data.Signal
import Data.BitVec

import Data.Nat
import Data.Signal

import Sym.Comb.Comb as CB
import Sym.Comb.CombPrimitive as CP

-- public export
interface CombL (comb: Type -> Type -> Type) where
  lam: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
    -> (comb () a -> comb () b) -> comb a b
  
  prod: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
     -> comb () a -> comb () b -> comb () (a, b)
     
  proj1: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
      -> comb () (a, b) -> comb () a
  
  proj2: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
      -> comb () (a, b) -> comb () b
      
  unit: comb () ()
  

public export
data E: (Type -> Type -> Type) -> Type -> Type -> Type where
  F: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
    -> (E comb () a -> E comb () b) -> E comb a b
  C: comb () a -> E comb () a
  
public export
{comb:_} -> (CombL comb) => Comb (E comb) where
  lam f = F f
  app (F f) e = f e
  app (C f) e = C f
  prod (F x) y = CB.prod {aIsSig = aIsSig} {bIsSig = bIsSig} (x unit) y
  prod x (F y) = CB.prod {aIsSig = aIsSig} {bIsSig = bIsSig} x (y unit)
  prod (C x) (C y) = C $ prod x y
  proj1 (F f) = CB.proj1 (f unit)
  proj1 (C x) = C $ proj1 x
  proj2 (F f) = CB.proj2 (f unit)
  proj2 (C x) = C $ proj2 x
  unit = C $ unit

public export
{comb:_} -> (CombL comb, Primitive comb) => Primitive (E comb) where  
  const x = C $ const x
  
  add (F f) y = add (f unit) y
  add x (F f) = add x (f unit)
  add (C x) (C y) = C $ add x y
  
  concat (F f) y = concat (f unit) y
  concat x (F f) = concat x (f unit)
  concat (C x) (C y) = C $ concat x y
  
  and (F f) y = and (f unit) y
  and x (F f) = and x (f unit)
  and (C x) (C y) = C $ and x y
  
  or (F f) y = or (f unit) y
  or x (F f) = or x (f unit)
  or (C x) (C y) = C $ or x y
  
  xor (F f) y = xor (f unit) y
  xor x (F f) = xor x (f unit)
  xor (C x) (C y) = C $ xor x y
  
  not (F f) = not (f unit)
  not (C x) = C $ not x
  
  slice l u (F f) = slice l u (f unit)
  slice l u (C x) = C $ slice l u x
  
  eq (F f) y = eq (f unit) y
  eq x (F f) = eq x (f unit)
  eq (C x) (C y) = C $ eq x y
  
  ltu (F f) y = ltu (f unit) y
  ltu x (F f) = ltu x (f unit)
  ltu (C x) (C y) = C $ ltu x y
  
  lt (F f) y = lt (f unit) y
  lt x (F f) = lt x (f unit)
  lt (C x) (C y) = C $ lt x y
  
  mux21 (F f) x y = mux21 (f unit) x y
  mux21 b (F f) y = mux21 b (f unit) y
  mux21 b x (F f) = mux21 b x (f unit)
  mux21 (C b) (C x) (C y) = C $ mux21 b x y
  
  shiftLL sht (F f) = shiftLL sht (f unit)
  shiftLL sht (C x) = C $ shiftLL sht x
  
  shiftRL sht (F f) = shiftRL sht (f unit)
  shiftRL sht (C x) = C $ shiftRL sht x
  
  shiftRA sht (F f) = shiftRA sht (f unit)
  shiftRA sht (C x) = C $ shiftRA sht x
  
refine: {comb: _} -> (CombL comb) 
     => E comb a b -> comb a b
refine (F f) = lam $ refine . f . C
refine (C x) = x

public export
data E0: (Type -> Type -> Type) 
      -> Type -> Type -> Type where
  U: comb a b -> E0 comb a b
  
generalise: E0 comb a b -> comb a b
generalise (U x) = x

public export
{comb:_} -> (Comb comb) => CombL (E0 comb) where
  lam f = U $ lam $ generalise . f . U
  prod (U x) (U y) = U $ CB.prod x y
  proj1 (U x) = U $ CB.proj1 x
  proj2 (U x) = U $ CB.proj2 x
  unit = U $ CB.unit

public export 
{comb:_} -> (Comb comb, Primitive comb) => Primitive (E0 comb) where  
  const x = U $ const x
  concat (U x) (U y) = U $ concat x y
  add (U x) (U y) = U $ add x y
  and (U x) (U y) = U $ and x y
  or (U x) (U y) = U $ or x y
  xor (U x) (U y) = U $ xor x y
  not (U x) = U $ not x
  slice l u (U x) = U $ slice l u x
  eq (U x) (U y) = U $ eq x y
  ltu (U x) (U y) = U $ ltu x y
  lt (U x) (U y) = U $ lt x y
  mux21 (U b) (U x) (U y) = U $ mux21 b x y
  shiftLL sht (U x) = U $ shiftLL sht x
  shiftRL sht (U x) = U $ shiftRL sht x
  shiftRA sht (U x) = U $ shiftRA sht x

public export  
normalise: {comb: _} -> (Comb comb) 
     => E (E0 comb) a b -> comb a b
normalise = generalise . refine 
