module Sym.Comb.CombLib

import Sym.Comb.Comb
import Sym.Comb.CombPrimitive

import Data.Nat
import Data.BitVec
import Data.Signal

%hide Prelude.Ops.infixr.(<|)

export
infixl 9 <|

export
infixl 9 |<

export
infixr 9 <<

export
infixr 9 <>

public export
lower: {n:_} -> (Comb comb, Primitive comb)
    => (m: Nat) -> {auto prf: LTE m n} -> comb (BitVec n) (BitVec m)
lower m = lam $ \x => rewrite sym $ minusZeroRight m in slice 0 m x

public export
lower': {n:_} -> (Primitive comb)
    => (m: Nat) -> {auto prf: LTE m n} 
    -> comb () (BitVec n) ->  comb () (BitVec m)
lower' m x = rewrite sym $ minusZeroRight m in slice 0 m x

-- Sequential Composition
public export
(<<): (Comb comb)
   => {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
   -> {auto cIsSig: Sig c}
   -> comb b c -> comb a b -> comb a c
(<<) g f = lam $ \x => app g $ app f x


-- Sequential Composition, bypass second
public export
(<|): {comb:_} -> (Comb comb)
   => {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
   -> {auto cIsSig: Sig c} -> {auto dIsSig: Sig d}
   -> comb (b, c) d -> comb a b -> comb (a, c) d
(<|) g f = lam $ \xs => app g 
                      $ prod (app f $ proj1 xs)
                             (proj2 xs)

-- Sequential Composition, bypass first
public export
(|<): {comb:_} -> (Comb comb)
   => {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
   -> {auto cIsSig: Sig c} -> {auto dIsSig: Sig d}
   -> comb (b, c) d -> comb a c -> comb (b, a) d
(|<) g f = lam $ \xs => app g 
                      $ prod (proj1 xs)
                             (app f $ proj2 xs)

-- Parallel Composition
public export
(<>): (Comb comb)
   => {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
   -> {auto cIsSig: Sig c} -> {auto dIsSig: Sig d}
   -> comb a b -> comb c d -> comb (a, c) (b, d)
(<>) f g = lam $ \xs => prod (app f $ proj1 xs) (app g $ proj2 xs)

public export
reduce: (Comb comb)
     => {auto prf1: Sig a}
     -> {auto prf2: All (OfType a) as}
     -> (f: comb (a, a) a)
     -> comb as a
reduce {prf2 = (AllU p)} f = 
  rewrite sym $ p in lam id
reduce {prf2 = (AllP p1 p2)} f = f << (reduce f) <> (reduce f)

public export
if_: (Comb comb, Primitive comb)
  => {auto aIsSig : Sig a}
  -> (b: comb () (BitVec 1)) 
  -> (x: comb () a) -> (y: comb () a)
  -> comb () a
if_ {aIsSig = U} b x y = unit
if_ {aIsSig = (P z w)} b x y = 
  prod (if_ b (proj1 x) (proj1 y))
       (if_ b (proj2 x) (proj2 y))
if_ {aIsSig = BV} b x y = mux21 b x y

repeat: (Comb comb)
     => {auto prf1: Sig a} 
     -> (n: Nat) -> comb a a -> comb a a
repeat 0 f = lam id
repeat (S k) f = f << (repeat k f)

public export
pointwise: (Comb comb, Primitive comb)
  => {auto aIsSig: Sig a} 
  -> {auto bIsSig: Sig b}
  -> {auto cIsSig: Sig c}
  -> {n: Nat}
  -> (comb () a -> comb () b -> comb () c)
  -> comb () (Repeat n a)
  -> comb () (Repeat n b) 
  -> comb () (Repeat n c)
pointwise {n = 0} f _ _   = unit
pointwise {n = (S 0)} f x y = f x y
pointwise {n = (S (S k))} f x y = 
  let p1 = repeatSig (S k) aIsSig
      p2 = repeatSig (S k) bIsSig
      p3 = repeatSig (S k) cIsSig
      hdx = proj1 x 
      tlx = proj2 x 
      hdy = proj1 y
      tly = proj2 y
  in prod (f hdx hdy) $ pointwise f tlx tly

-- Linear reduce
example1: {n:_} -> {comb:_} -> (Comb comb)
       => (f: comb (BitVec n, BitVec n) (BitVec n))
       -> comb (BitVec n, BitVec n, BitVec n, BitVec n) 
               (BitVec n)
example1 = reduce 

-- Balance reduce
example2: {n:_} -> {comb:_} -> (Comb comb)
       => (f: comb (BitVec n, BitVec n) (BitVec n))
       -> comb ((BitVec n, BitVec n), (BitVec n, BitVec n)) 
               (BitVec n)
example2 = reduce

-- match structures, a = (bv n, bv n)
example3: {n:_} -> {comb:_} -> (Comb comb)
       => (f: comb ((BitVec n, BitVec n), (BitVec n, BitVec n)) 
                   (BitVec n, BitVec n))
       -> comb ((BitVec n, BitVec n), (BitVec n, BitVec n), (BitVec n, BitVec n)) 
               (BitVec n, BitVec n)
example3 = reduce

reduce2: {comb:_} -> (Comb comb)
     => {auto prf1: Sig a}
     -> {auto prf2: All (OfType a) as}
     -> (f: comb (a, a) a)
     -> comb as a
reduce2 {prf2 = (AllU p)} f = 
  rewrite sym $ p in lam id
reduce2 {prf2 = (AllP p1 p2)} f = f <| (reduce2 f) |< (reduce2 f)


lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

public export
adder: {n:_} 
  -> (Comb comb, Primitive comb)
  => comb (BitVec n, BitVec n) (BitVec n)
adder = lam $ \x => lower' {prf=lteSucc n} n (add (proj1 x) (proj2 x))

public export
adder': {n:_} 
  -> (Primitive comb)
  => comb () (BitVec n)
  -> comb () (BitVec n) 
  -> comb () (BitVec n)
adder' x y = lower' {prf=lteSucc n} n $ add x y
